#include "runloop_monad.hpp"
#include "event.hpp"

#include <monad/chain/chain.hpp>
#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_types.h>
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

#include <bit>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <iterator>
#include <memory>
#include <optional>
#include <thread>
#include <vector>

namespace fs = std::filesystem;

extern fs::path event_rtt_export_path;

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

    bytes32_t
    bft_id_for_finalized_block(mpt::Db const &db, uint64_t const block_id)
    {

        auto encoded_bft_header =
            db.get(mpt::concat(FINALIZED_NIBBLE, BFT_BLOCK_NIBBLE), block_id);
        MONAD_ASSERT(encoded_bft_header.has_value());
        return to_bytes(blake3(encoded_bft_header.value()));
    }

}

Result<BlockExecOutput> on_proposal_event(
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
    BlockExecOutput exec_output;
    BOOST_OUTCOME_TRY(
        exec_output.tx_exec_results,
        execute_block(
            chain, rev, block, block_state, block_hash_buffer, priority_pool));

    block_state.log_debug();
    block_state.commit(
        consensus_header,
        block.transactions,
        exec_output.tx_exec_results,
        block.ommers,
        block.withdrawals);
    exec_output.eth_header = db.read_eth_header();
    BOOST_OUTCOME_TRY(
        chain.validate_output_header(block.header, exec_output.eth_header));

    exec_output.eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));

    return exec_output;
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
    mpt::Db const &raw_db, Db &db, BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &finalized_block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop)
{
    using event_round_trip_test::ExpectedDataRecorder;
    constexpr auto SLEEP_TIME = std::chrono::microseconds(100);
    std::unique_ptr<ExpectedDataRecorder> rtt_recorder;

    if (!event_rtt_export_path.empty()) {
        rtt_recorder =
            std::make_unique<ExpectedDataRecorder>(event_rtt_export_path);
    }

    WalReader reader(ledger_dir);
    if (finalized_block_num > 1) { // no wal entry for genesis
        auto const bft_block_id =
            bft_id_for_finalized_block(raw_db, finalized_block_num - 1);
        WalEntry const entry{.action = WalAction::PROPOSE, .id = bft_block_id};
        if (reader.rewind_to(entry)) {
            reader.next(); // skip proposal
        }
    }
    BlockHashChain block_hash_chain(block_hash_buffer);

    uint64_t total_gas = 0;
    uint64_t ntxs = 0;
    uint64_t const start_block_num = finalized_block_num;

    while (finalized_block_num <= end_block_num && stop == 0) {
        auto const reader_res = reader.next();
        if (!reader_res.has_value()) {
            std::this_thread::sleep_for(SLEEP_TIME);
            continue;
        }

        auto [action, consensus_header, consensus_body, bft_block_id] =
            reader_res.value();
        auto const block_number = consensus_header.execution_inputs.number;
        if (action == WalAction::PROPOSE) {
            auto const block_time_start = std::chrono::steady_clock::now();

            auto const ntxns = consensus_body.transactions.size();
            auto const &block_hash_buffer =
                block_hash_chain.find_chain(consensus_header.parent_round());

            // Initialize and record the BLOCK_START event; the matching end
            // event is recorded by the try_record_block_exec_output helper
            // function
            monad_event_block_exec_header *exec_header =
                monad_event_recorder_alloc_block_exec_header();
            init_block_exec_header(
                bft_block_id,
                consensus_header,
                size(consensus_body.transactions),
                exec_header);
            monad_event_recorder_start_block(exec_header);

            BOOST_OUTCOME_TRY(
                BlockExecOutput const exec_output,
                try_record_block_exec_output(
                    bft_block_id,
                    consensus_header,
                    consensus_body.transactions,
                    on_proposal_event(
                        consensus_header,
                        Block{
                            .header = consensus_header.execution_inputs,
                            .transactions = consensus_body.transactions,
                            .ommers = std::move(consensus_body.ommers),
                            .withdrawals = std::move(consensus_body.withdrawals)},
                        block_hash_buffer,
                        chain,
                        db,
                        priority_pool,
                        block_number == start_block_num),
                    rtt_recorder.get()));

            block_hash_chain.propose(
                exec_output.eth_block_hash,
                consensus_header.round,
                consensus_header.parent_round());

            log_tps(
                block_number,
                consensus_header.round,
                ntxns,
                exec_output.eth_header.gas_used,
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

            monad_event_block_finalize const finalize_info = {
                .bft_block_id =
                    std::bit_cast<monad_event_bytes32>(bft_block_id),
                .consensus_seqno = consensus_header.seqno};
            MONAD_EVENT_EXPR(MONAD_EVENT_BLOCK_FINALIZE, 0, finalize_info);
            monad_event_recorder_clear_block_id();
            if (rtt_recorder) {
                rtt_recorder->record_finalization(bft_block_id);
            }
        }
        else {
            MONAD_ABORT_PRINTF(
                "Unknown action %u", static_cast<uint8_t>(action));
        }
    }

    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
