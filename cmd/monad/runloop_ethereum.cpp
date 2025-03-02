#include "runloop_ethereum.hpp"
#include "event.hpp"

#include <monad/chain/chain.hpp>
#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/event/exec_event_recorder.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/monad_block_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <quill/Quill.h>

#include <algorithm>
#include <array>
#include <chrono>
#include <span>

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

// Processing a block encompasses all the following actions:
//
//   1. block header input validation
//   2. sender address recovery
//   3. "core" execution: transaction-level EVM execution that tracks state
//      changes, but does not commit them
//   4. database commit of state changes (incl. Merkle root calculations)
//   5. post-commit validation of header, with Merkle root fields filled in
//   6. computation of block hash, appending it to the circular hash buffer
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

    size_t const transaction_count = block.transactions.size();
    std::vector<boost::fibers::promise<void>> txn_sync_barriers(
        transaction_count);
    auto const recovered_senders =
        recover_senders(block.transactions, priority_pool, txn_sync_barriers);
    std::vector<Address> senders(transaction_count);
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        if (recovered_senders[i].has_value()) {
            senders[i] = recovered_senders[i].value();
        }
        else {
            return TransactionError::MissingSender;
        }
    }

    // Ethereum: always execute off of the parent proposal round, commit to
    // `round = block_number`, and finalize immediately after that.
    db.set_block_and_round(block.header.number - 1, round_number);

    BlockExecOutput exec_output;
    BlockState block_state(db);
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_PERF_EVM_ENTER);
    BOOST_OUTCOME_TRY(
        auto results,
        execute_block(
            chain,
            rev,
            block,
            senders,
            block_state,
            block_hash_buffer,
            priority_pool,
            txn_sync_barriers));
    record_exec_event(std::nullopt, MONAD_EXEC_BLOCK_PERF_EVM_EXIT);

    std::vector<Receipt> receipts(results.size());
    std::vector<std::vector<CallFrame>> call_frames(results.size());
    for (unsigned i = 0; i < results.size(); ++i) {
        auto &result = results[i];
        receipts[i] = std::move(result.receipt);
        call_frames[i] = std::move(result.call_frames);
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

// TODO(ken): this is a configuration parameter for Consensus (it is
//    currently three) but we're hardcoding it
constexpr unsigned EXECUTION_DELAY = 3;

template <std::size_t N>
class ConsensusHeaderRing
{
public:
    explicit ConsensusHeaderRing(uint64_t start_block_num, BlockDb const &);

    std::pair<bytes32_t const &, MonadConsensusBlockHeader const &>
    lookback(uint64_t n)
    {
        MONAD_ASSERT(items_ >= n && n <= N);
        return {block_ids_[(items_ - n) % N], headers_[(items_ - n) % N]};
    }

    void set_next(bytes32_t bft_block_id, MonadConsensusBlockHeader header)
    {
        block_ids_[items_ % N] = std::move(bft_block_id);
        headers_[items_ % N] = std::move(header);
        ++items_;
    }

private:
    uint64_t start_block_num_;
    uint64_t items_;
    std::array<bytes32_t, N> block_ids_;
    std::array<MonadConsensusBlockHeader, N> headers_;
};

template <std::size_t N>
ConsensusHeaderRing<N>::ConsensusHeaderRing(
    uint64_t start_block_num, BlockDb const &block_db)
    : start_block_num_{start_block_num}
    , items_{0}
{
    for (uint64_t lookback = N; lookback > 0; --lookback) {
        if (lookback > start_block_num_) {
            // Special case: we can't look past the genesis block
            continue;
        }
        Block ancestor_block;
        uint64_t const ancestor_block_num = start_block_num_ - lookback;
        bool const block_ok = block_db.get(ancestor_block_num, ancestor_block);
        MONAD_ASSERT_PRINTF(
            block_ok,
            "Could not load ancestor block %lu from BlockDb",
            ancestor_block_num);
        MonadConsensusBlockHeader consensus_header;
        if (items_ == 0) {
            consensus_header = MonadConsensusBlockHeader::from_eth_header(
                ancestor_block.header, ancestor_block_num);
            consensus_header.delayed_execution_results.clear();
        }
        else {
            auto const &[prev_hash, prev_consensus_header] = this->lookback(1);
            consensus_header = MonadConsensusBlockHeader::from_eth_header_next(
                ancestor_block.header,
                prev_consensus_header,
                prev_hash,
                EXECUTION_DELAY);
        }
        auto const r = rlp::encode_consensus_block_header(consensus_header);
        this->set_next(to_bytes(blake3(r)), consensus_header);
    }
}

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &chain, std::filesystem::path const &ledger_dir, Db &db,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop)
{
    uint64_t const batch_size =
        end_block_num == std::numeric_limits<uint64_t>::max() ? 1 : 1000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;

    uint64_t const start_block_num = block_num;
    uint256_t const chain_id = chain.get_chain_id();
    BlockDb block_db(ledger_dir);

    // To emulate the pipelined operation of the Monad consensus algorithm
    // during Ethereum historical replay, we keep track of the two previous
    // blocks. Before executing a proposal, we'll finalize the block from two
    // rounds earlier
    constexpr size_t MAX_LOOKBACK = 2;
    ConsensusHeaderRing<MAX_LOOKBACK> consensus_block_history{
        start_block_num, block_db};

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

        // Derive the next consensus header from the combination of the
        // previous consensus header and the Ethereum block header
        auto const &[prev_hash, prev_consensus_header] =
            consensus_block_history.lookback(1);
        auto consensus_header = MonadConsensusBlockHeader::from_eth_header_next(
            block.header, prev_consensus_header, prev_hash, EXECUTION_DELAY);
        auto const consensus_header_rlp =
            rlp::encode_consensus_block_header(consensus_header);
        bytes32_t const bft_block_id = to_bytes(blake3(consensus_header_rlp));

        // Finalize the proposal from 2 rounds ago. This also writes the
        // BLOCK_VERIFIED event
        if (block_num > 1) {
            auto const &[id, h] = consensus_block_history.lookback(2);
            if (id != bytes32_t{} && !h.delayed_execution_results.empty()) {
                record_block_finalized(id, h);
            }
        }

        // Record the BLOCK_QC event for this round's QC and the BLOCK_START
        // event that marks the beginning of this proposed block's execution
        record_block_exec_start(
            bft_block_id,
            chain_id,
            consensus_header,
            consensus_header.execution_inputs.parent_hash,
            size(block.transactions));

        // Call the main block execution subroutine and record the results
        BOOST_OUTCOME_TRY(
            BlockExecOutput const exec_output,
            record_block_exec_result(process_ethereum_block(
                chain,
                db,
                block_hash_buffer,
                priority_pool,
                consensus_header,
                block,
                round_number)));

        // Update history for the next round
        consensus_block_history.set_next(
            std::move(bft_block_id), std::move(consensus_header));

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
