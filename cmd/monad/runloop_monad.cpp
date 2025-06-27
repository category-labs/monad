#include "runloop_monad.hpp"
#include "file_io.hpp"

#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
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
#include <monad/execution/validate_transaction.hpp>
#include <monad/execution/wal_reader.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/db.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>

#include <boost/outcome/try.hpp>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <filesystem>
#include <optional>
#include <thread>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

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
            std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
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

void init_block_hash_chain_proposals(
    mpt::Db &db, BlockHashChain &block_hash_chain,
    uint64_t const start_block_num)
{
    uint64_t const end_block_num = db.get_latest_block_id();
    for (uint64_t b = start_block_num; b <= end_block_num; ++b) {
        for (uint64_t const r : get_proposal_rounds(db, b)) {
            auto const consensus_header =
                read_consensus_header(db, b, proposal_prefix(r));
            MONAD_ASSERT_PRINTF(
                consensus_header.has_value(),
                "Could not decode consensus block at (%lu, %lu)",
                b,
                r);
            auto const encoded_eth_header =
                db.get(mpt::concat(proposal_prefix(r), BLOCKHEADER_NIBBLE), b);
            MONAD_ASSERT(encoded_eth_header.has_value());
            block_hash_chain.propose(
                to_bytes(keccak256(encoded_eth_header.value())),
                consensus_header.value().round,
                consensus_header.value().parent_round());
        }
    }
}

bool has_executed(mpt::Db const &db, MonadConsensusBlockHeader const &header)
{
    auto const prefix = proposal_prefix(header.round);
    return header == read_consensus_header(db, header.seqno, prefix);
}

bool validate_delayed_execution_results(
    BlockHashBuffer const &block_hash_buffer,
    std::vector<BlockHeader> const &execution_results)
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

        auto const block_hash =
            to_bytes(keccak256(rlp::encode_block_header(result)));
        if (MONAD_UNLIKELY(
                block_hash != block_hash_buffer.get(result.number))) {
            LOG_ERROR(
                "Delayed execution result mismatch for block {}",
                result.number);
            return false;
        }
        expected_block_number = result.number + 1;
    }
    return true;
}

Result<std::pair<bytes32_t, uint64_t>> propose_block(
    MonadConsensusBlockHeader const &consensus_header, Block block,
    BlockHashChain &block_hash_chain, Chain const &chain, Db &db, vm::VM &vm,
    fiber::PriorityPool &priority_pool, bool const is_first_block)
{
    auto const &block_hash_buffer =
        block_hash_chain.find_chain(consensus_header.parent_round());

    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

    evmc_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);

    BOOST_OUTCOME_TRY(static_validate_block(rev, block));

    db.set_block_and_round(
        block.header.number - 1,
        is_first_block ? std::nullopt
                       : std::make_optional(consensus_header.parent_round()));

    auto const recovered_senders =
        recover_senders(block.transactions, priority_pool);
    std::vector<Address> senders(block.transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        if (recovered_senders[i].has_value()) {
            senders[i] = recovered_senders[i].value();
        }
        else {
            return TransactionError::MissingSender;
        }
    }
    BlockState block_state(db, vm);
    BOOST_OUTCOME_TRY(
        auto results,
        execute_block(
            chain,
            rev,
            block,
            senders,
            block_state,
            block_hash_buffer,
            priority_pool));

    std::vector<Receipt> receipts(results.size());
    std::vector<std::vector<CallFrame>> call_frames(results.size());
    for (unsigned i = 0; i < results.size(); ++i) {
        auto &result = results[i];
        receipts[i] = std::move(result.receipt);
        call_frames[i] = (std::move(result.call_frames));
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

    auto const block_hash =
        to_bytes(keccak256(rlp::encode_block_header(output_header)));

    return std::make_pair(block_hash, output_header.gas_used);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    Chain const &chain, std::filesystem::path const &ledger_dir,
    mpt::Db &raw_db, Db &db, vm::VM &vm,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &finalized_block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop)
{
    constexpr auto SLEEP_TIME = std::chrono::microseconds(100);
    uint64_t const start_block_num = finalized_block_num;
    BlockHashChain block_hash_chain(block_hash_buffer);
    init_block_hash_chain_proposals(raw_db, block_hash_chain, start_block_num);

    auto const body_dir = ledger_dir / "bodies";
    auto const header_dir = ledger_dir / "headers";
    auto const proposed_head = header_dir / "proposed_head";
    auto const finalized_head = header_dir / "finalized_head";

    uint64_t total_gas = 0;
    uint64_t ntxs = 0;

    struct ToFinalize
    {
        uint64_t block;
        uint64_t round;
        uint64_t verified_block;
    };

    std::deque<MonadConsensusBlockHeader> to_execute;
    std::deque<ToFinalize> to_finalize;

    MONAD_ASSERT(
        raw_db.get_latest_finalized_block_id() != mpt::INVALID_BLOCK_ID);

    while (finalized_block_num < end_block_num && stop == 0) {
        bytes32_t id;
        MonadConsensusBlockHeader header;
        to_finalize.clear();
        to_execute.clear();

        uint64_t const last_finalized_by_execution =
            raw_db.get_latest_finalized_block_id();

        // read from finalized head if we are behind
        id = head_pointer_to_id(finalized_head);
        if (MONAD_LIKELY(id != bytes32_t{})) {
            do {
                header = read_header(id, header_dir);
                id = header.parent_id();

                if (MONAD_UNLIKELY(header.seqno > end_block_num)) {
                    continue;
                }
                bool const needs_finalize =
                    header.seqno > last_finalized_by_execution;
                if (needs_finalize) {
                    uint64_t const verified_block =
                        header.delayed_execution_results.empty()
                            ? 0
                            : header.delayed_execution_results.back().number;
                    to_finalize.push_front(ToFinalize{
                        .block = header.seqno,
                        .round = header.round,
                        .verified_block = verified_block});
                }

                if (!has_executed(raw_db, header)) {
                    MONAD_ASSERT(needs_finalize);
                    to_execute.push_front(std::move(header));
                }
            }
            while (header.seqno - 1 > last_finalized_by_execution);
        }

        // try reading from proposal head if we are caught up
        if (to_finalize.empty()) {
            id = head_pointer_to_id(proposed_head);
            if (MONAD_LIKELY(id != bytes32_t{})) {
                do {
                    header = read_header(id, header_dir);
                    if (header.seqno <= end_block_num &&
                        !has_executed(raw_db, header)) {
                        to_execute.push_front(std::move(header));
                    }
                    id = header.parent_id();
                }
                while (header.seqno - 1 > last_finalized_by_execution);

                // Before executing this proposal chain, verify we are on the
                // canonical chain. Note that this condition doesn't hold when
                // no blocks have been finalized because consensus starts at
                // block 1 with a parent_id of 0x0, but will work after the
                // finalized_head points to a block with seqno >= 1.
                if (!to_execute.empty()) {
                    bool const on_canonical_chain =
                        query_consensus_header(
                            raw_db, header.seqno - 1, finalized_nibbles)
                            .transform(
                                [&header](byte_string const &header_data) {
                                    return to_bytes(blake3(header_data)) ==
                                           header.parent_id();
                                })
                            .value_or(false);
                    if (MONAD_UNLIKELY(!on_canonical_chain)) {
                        to_execute.clear();
                    }
                }
            }
        }

        if (MONAD_UNLIKELY(to_execute.empty() && to_finalize.empty())) {
            std::this_thread::sleep_for(SLEEP_TIME);
            continue;
        }

        for (auto const &consensus_header : to_execute) {
            auto const block_time_start = std::chrono::steady_clock::now();

            uint64_t const block_number =
                consensus_header.execution_inputs.number;
            MonadConsensusBlockBody const consensus_body =
                read_body(consensus_header.block_body_id, body_dir);
            auto const ntxns = consensus_body.transactions.size();

            auto const &block_hash_buffer =
                block_hash_chain.find_chain(consensus_header.parent_round());

            MONAD_ASSERT(validate_delayed_execution_results(
                block_hash_buffer, consensus_header.delayed_execution_results));

            BOOST_OUTCOME_TRY(
                auto const propose_result,
                propose_block(
                    consensus_header,
                    Block{
                        .header = consensus_header.execution_inputs,
                        .transactions = std::move(consensus_body.transactions),
                        .ommers = std::move(consensus_body.ommers),
                        .withdrawals = std::move(consensus_body.withdrawals)},
                    block_hash_chain,
                    chain,
                    db,
                    vm,
                    priority_pool,
                    block_number == start_block_num));
            auto const &[block_hash, gas_used] = propose_result;
            block_hash_chain.propose(
                block_hash,
                consensus_header.round,
                consensus_header.parent_round());

            db.update_proposed_metadata(block_number, consensus_header.round);
            db.update_voted_metadata(
                consensus_header.seqno - 1, consensus_header.qc.vote.round);

            log_tps(
                block_number,
                consensus_header.round,
                ntxns,
                gas_used,
                block_time_start);
        }

        for (auto const [block, round, verified_block] : to_finalize) {
            LOG_INFO(
                "Processing finalization for block {} at round {}",
                block,
                round);
            db.finalize(block, round);
            block_hash_chain.finalize(round);
            db.update_verified_block(verified_block);
            finalized_block_num = block;
        }
    }

    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
