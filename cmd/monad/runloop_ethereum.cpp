#include "runloop_ethereum.hpp"
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
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_types.h>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>

#include <boost/outcome/try.hpp>
#include <quill/Quill.h>

#include <bit>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <filesystem>
#include <iterator>
#include <limits>
#include <memory>
#include <optional>
#include <vector>

extern std::filesystem::path event_rtt_export_path;

MONAD_NAMESPACE_BEGIN

namespace
{

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

    void log_tps(
        uint64_t const block_num, uint64_t const nblocks, uint64_t const ntxs,
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
            "Run {:4d} blocks to {:8d}, number of transactions {:6d}, "
            "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
            nblocks,
            block_num,
            ntxs,
            tps,
            gps,
            monad_procfs_self_resident() / (1L << 20));
    };

#pragma GCC diagnostic pop
}

// Execute a single block; the generic term "process" is used to avoid using
// the overloaded term "execute" again; encompasses all the following actions:
//
//   1. block header input validation
//   2. "core" execution: transaction-level EVM execution that tracks state
//      changes, but does not commit them)
//   3. database commit of state changes (incl. Merkle root calculations)
//   4. post-commit validation of header, with Merkle root fields filled in
//   5. computation of block hash, appending it to the circular hash buffer
static Result<BlockExecOutput> process_ethereum_block(
    Chain const &chain, Db &db, BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool,
    MonadConsensusBlockHeader const &consensus_header, Block &block,
    std::optional<uint64_t> round_number)
{
    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));

    evmc_revision const rev =
        chain.get_revision(block.header.number, block.header.timestamp);

    BOOST_OUTCOME_TRY(static_validate_block(rev, block));

    // Ethereum: always execute off of the parent proposal round, commit to
    // `round = block_number`, and finalize immediately after that.
    db.set_block_and_round(block.header.number - 1, round_number);

    BlockExecOutput exec_output;
    BlockState block_state(db);
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

    db.finalize(block.header.number, block.header.number);
    db.update_verified_block(block.header.number);

    exec_output.eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(exec_output.eth_header)));
    block_hash_buffer.set(
        exec_output.eth_header.number, exec_output.eth_block_hash);

    return exec_output;
}

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &chain, std::filesystem::path const &ledger_dir, Db &db,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop)
{
    using event_round_trip_test::ExpectedDataRecorder;
    std::unique_ptr<ExpectedDataRecorder> rtt_recorder;
    uint64_t const batch_size =
        end_block_num == std::numeric_limits<uint64_t>::max() ? 1 : 1000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;

    uint64_t const start_block_num = block_num;

    if (!event_rtt_export_path.empty()) {
        rtt_recorder =
            std::make_unique<ExpectedDataRecorder>(event_rtt_export_path);
    }

    BlockDb block_db(ledger_dir);
    while (block_num <= end_block_num && stop == 0) {
        Block block;
        MONAD_ASSERT_PRINTF(
            block_db.get(block_num, block),
            "Could not query %lu from blockdb",
            block_num);

        std::optional<uint64_t> const round_number =
            block.header.number == start_block_num
                ? std::nullopt
                : std::make_optional(block.header.number - 1);

        // First derive a MonadConsensusBlockHeader for this Ethereum block
        // immediately, since the event recording protocol expects one.
        auto const consensus_header =
            MonadConsensusBlockHeader::from_eth_header(block.header);
        auto const consensus_header_rlp =
            rlp::encode_consensus_block_header(consensus_header);
        bytes32_t const bft_block_id =
            std::bit_cast<bytes32_t>(blake3(consensus_header_rlp));

        monad_event_block_exec_header *exec_header =
            monad_event_recorder_alloc_block_exec_header();
        init_block_exec_header(
            bft_block_id,
            consensus_header,
            size(block.transactions),
            exec_header);
        monad_event_recorder_start_block(exec_header);

        // Call the main block execution subroutine and record the results
        BOOST_OUTCOME_TRY(
            BlockExecOutput const exec_output,
            try_record_block_exec_output(
                bft_block_id,
                consensus_header,
                block.transactions,
                process_ethereum_block(
                    chain,
                    db,
                    block_hash_buffer,
                    priority_pool,
                    consensus_header,
                    block,
                    round_number),
                rtt_recorder.get()));

        // runloop_ethereum is only used for historical replay, so blocks are
        // finalized immediately
        monad_event_block_finalize const finalize_info = {
            .bft_block_id = std::bit_cast<monad_event_bytes32>(bft_block_id),
            .consensus_seqno = consensus_header.seqno};
        MONAD_EVENT_EXPR(MONAD_EVENT_BLOCK_FINALIZE, 0, finalize_info);
        monad_event_recorder_clear_block_id();
        if (rtt_recorder) {
            rtt_recorder->record_finalization(bft_block_id);
        }

        ntxs += block.transactions.size();
        batch_num_txs += block.transactions.size();
        total_gas += block.header.gas_used;
        batch_gas += block.header.gas_used;
        ++batch_num_blocks;

        if (block_num % batch_size == 0) {
            log_tps(
                block_num,
                batch_num_blocks,
                batch_num_txs,
                batch_gas,
                batch_begin);
            batch_num_blocks = 0;
            batch_num_txs = 0;
            batch_gas = 0;
            batch_begin = std::chrono::steady_clock::now();
        }
        ++block_num;
    }
    if (batch_num_blocks > 0) {
        log_tps(
            block_num, batch_num_blocks, batch_num_txs, batch_gas, batch_begin);
    }
    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
