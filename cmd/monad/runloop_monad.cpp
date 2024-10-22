#include "runloop_monad.hpp"

#include <monad/chain/chain.hpp>
#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/wal_reader.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/db.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>

#include <boost/outcome/try.hpp>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <optional>
#include <thread>
#include <vector>

namespace fs = std::filesystem;

MONAD_NAMESPACE_BEGIN

namespace
{

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

    void log_tps(
        uint64_t const block_num, uint64_t const round_num, uint64_t const ntxs,
        uint64_t const gas, std::chrono::steady_clock::time_point const begin)
    {
        auto const now = std::chrono::steady_clock::now();
        auto const elapsed = std::max(
            static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::microseconds>(
                    now - begin)
                    .count()),
            1UL); // for the unlikely case that elapsed < 1 mic
        uint64_t const tps = (ntxs) * 1'000'000 / elapsed;
        uint64_t const gps = gas / elapsed;

        LOG_INFO(
            "Run to block= {:4d}, round= {:4d}, number of transactions {:6d}, "
            "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
            block_num,
            round_num,
            ntxs,
            tps,
            gps,
            monad_procfs_self_resident() / (1L << 20));
    };

#pragma GCC diagnostic pop

    std::optional<bytes32_t>
    bft_id_for_finalized_block(mpt::Db const &db, uint64_t const block_id)
    {

        auto encoded_bft_header =
            db.get(mpt::concat(FINALIZED_NIBBLE, BFT_BLOCK_NIBBLE), block_id);
        if (!encoded_bft_header.has_value()) {
            return std::nullopt;
        }
        return to_bytes(blake3(encoded_bft_header.value()));
    }

}

Result<std::pair<bytes32_t, uint64_t>> on_proposal_event(
    MonadConsensusBlockHeader const &consensus_header, Block block,
    BlockHashBuffer const &block_hash_buffer, Chain const &chain, Db &db,
    fiber::PriorityPool &priority_pool, bool const is_first_block)
{
    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

    evmc_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);

    BOOST_OUTCOME_TRY(static_validate_block(rev, block));

    db.set_block_and_round(
        block.header.number - 1,
        is_first_block ? std::nullopt
                       : std::make_optional(consensus_header.parent_round()));

    BlockState block_state(db);
    BOOST_OUTCOME_TRY(
        auto results,
        execute_block(
            chain, rev, block, block_state, block_hash_buffer, priority_pool));

    std::vector<Receipt> receipts(results.size());
    std::vector<std::vector<CallFrame>> call_frames(results.size());
    std::vector<Address> senders(results.size());
    for (unsigned i = 0; i < results.size(); ++i) {
        auto &result = results[i];
        receipts[i] = std::move(result.receipt);
        call_frames[i] = (std::move(result.call_frames));
        senders[i] = result.sender;
    }

    block_state.log_debug();
    block_state.commit(
        consensus_header,
        receipts,
        call_frames,
        senders,
        block.transactions,
        block.ommers,
        block.withdrawals);
    auto const output_header = db.read_eth_header();
    BOOST_OUTCOME_TRY(
        chain.validate_output_header(block.header, output_header));

    return {
        to_bytes(keccak256(rlp::encode_block_header(output_header))),
        output_header.gas_used};
}

bool validate_delayed_execution_results(
    Db &db, std::vector<BlockHeader> const &execution_results)
{
    if (MONAD_UNLIKELY(execution_results.empty())) {
        return true;
    }

    uint64_t expected_block_number = execution_results.front().number;
    for (auto const &result : execution_results) {
        if (MONAD_UNLIKELY(expected_block_number != result.number)) {
            LOG_ERROR(
                "Validated blocks not increasing. Expected block {}, got block "
                "{}",
                expected_block_number,
                result.number);
            return false;
        }

        db.set_block_and_round(result.number);
        if (MONAD_UNLIKELY(db.read_eth_header() != result)) {
            LOG_ERROR(
                "Delayed execution result mismatch for block {}",
                result.number);
            return false;
        }

        expected_block_number = result.number + 1;
    }
    return true;
}

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    Chain const &chain, std::filesystem::path const &ledger_dir,
    mpt::Db &raw_db, Db &db, BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &finalized_block_num,
    uint64_t const end_block_num, std::atomic<bool> const &stop)
{
    constexpr auto SLEEP_TIME = std::chrono::microseconds(100);

    WalReader reader(ledger_dir);
    if (finalized_block_num > 1) { // no wal entry for genesis
        raw_db.update_voted_metadata(
            mpt::INVALID_BLOCK_ID, mpt::INVALID_ROUND_NUM);
        auto const bft_block_id =
            bft_id_for_finalized_block(raw_db, finalized_block_num - 1);
        if (bft_block_id.has_value()) {
            WalEntry const entry{
                .action = WalAction::PROPOSE, .id = bft_block_id.value()};
            if (reader.rewind_to(entry)) {
                reader.next(); // skip proposal
            }
        }
    }
    BlockHashChain block_hash_chain(block_hash_buffer);

    uint64_t total_gas = 0;
    uint64_t ntxs = 0;
    uint64_t const start_block_num = finalized_block_num;
    while (finalized_block_num <= end_block_num &&
           stop.load(std::memory_order_relaxed) == 0) {
        auto const reader_res = reader.next();
        if (!reader_res.has_value()) {
            std::this_thread::sleep_for(SLEEP_TIME);
            continue;
        }

        auto [action, consensus_header, consensus_body] = reader_res.value();
        auto const block_number = consensus_header.execution_inputs.number;
        if (action == WalAction::PROPOSE) {
            auto const block_time_start = std::chrono::steady_clock::now();

            auto const ntxns = consensus_body.transactions.size();
            auto const &block_hash_buffer =
                block_hash_chain.find_chain(consensus_header.parent_round());
            BOOST_OUTCOME_TRY(
                auto const proposal_output,
                on_proposal_event(
                    consensus_header,
                    Block{
                        .header = consensus_header.execution_inputs,
                        .transactions = std::move(consensus_body.transactions),
                        .ommers = std::move(consensus_body.ommers),
                        .withdrawals = std::move(consensus_body.withdrawals)},
                    block_hash_buffer,
                    chain,
                    db,
                    priority_pool,
                    block_number == start_block_num));
            auto const &[output_header, gas_used] = proposal_output;
            block_hash_chain.propose(
                output_header,
                consensus_header.round,
                consensus_header.parent_round());
            db.update_voted_metadata(
                consensus_header.seqno - 1, consensus_header.qc.vote.round);

            log_tps(
                block_number,
                consensus_header.round,
                ntxns,
                gas_used,
                block_time_start);
        }
        else if (action == WalAction::FINALIZE) {
            LOG_INFO(
                "Processing finalization for block {} at round {}",
                block_number,
                consensus_header.round);
            db.finalize(block_number, consensus_header.round);
            block_hash_chain.finalize(consensus_header.round);

            auto const &verified_blocks =
                consensus_header.delayed_execution_results;
            MONAD_ASSERT(
                validate_delayed_execution_results(db, verified_blocks));
            if (MONAD_LIKELY(!verified_blocks.empty())) {
                db.update_verified_block(verified_blocks.back().number);
            }
            finalized_block_num = block_number;
        }
        else {
            MONAD_ABORT_PRINTF(
                "Unknown action %u", static_cast<uint8_t>(action));
        }
    }

    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
