// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "runloop_ethereum.hpp"

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/core/procfs/statm.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/outcome/try.hpp>
#include <quill/Quill.h>

#include <algorithm>
#include <chrono>
#include <memory>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct BatchStats
{
    uint64_t num_retries = 0;
    std::chrono::microseconds sender_recovery_time{0};
    std::chrono::microseconds tx_exec_time{0};
    std::chrono::microseconds commit_time{0};
};

void log_tps(
    uint64_t const block_num, uint64_t const nblocks, uint64_t const ntxs,
    uint64_t const gas, std::chrono::steady_clock::time_point const begin,
    BatchStats const &stats)
{
    auto const now = std::chrono::steady_clock::now();
    auto const elapsed = std::max(
        static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
                .count()),
        1UL);
    uint64_t const tps = ntxs * 1'000'000 / elapsed;
    uint64_t const gps = gas / elapsed;

    LOG_INFO(
        "batch,bl={:8},nbl={:4},tx={:6}"
        ",rt={:5},rtp={:5.2f}%"
        ",sr={:>9},txe={:>10},cmt={:>10},tot={:>10}"
        ",tps={:5},gps={:4},rss={:6}",
        block_num,
        nblocks,
        ntxs,
        stats.num_retries,
        100.0 * (double)stats.num_retries / std::max(1.0, (double)ntxs),
        stats.sender_recovery_time,
        stats.tx_exec_time,
        stats.commit_time,
        std::chrono::microseconds(elapsed),
        tps,
        gps,
        monad_procfs_self_resident() / (1L << 20));
}

struct BlockStats
{
    uint64_t num_retries;
    std::chrono::microseconds sender_recovery_time;
    std::chrono::microseconds tx_exec_time;
    std::chrono::microseconds commit_time;
};

// Process a single historical Ethereum block
template <Traits traits>
Result<BlockStats> process_ethereum_block(
    Chain const &chain, Db &db, vm::VM &vm,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, Block &block, bytes32_t const &block_id,
    bytes32_t const &parent_block_id, bool const enable_tracing)
{
    [[maybe_unused]] auto const block_start = std::chrono::system_clock::now();

    // Block input validation
    BOOST_OUTCOME_TRY(chain.static_validate_header(block.header));
    BOOST_OUTCOME_TRY(static_validate_block<traits>(block));

    // Sender and authority recovery
    auto const sender_recovery_begin = std::chrono::steady_clock::now();
    auto const recovered_senders =
        recover_senders(block.transactions, priority_pool);
    auto const recovered_authorities =
        recover_authorities(block.transactions, priority_pool);
    [[maybe_unused]] auto const sender_recovery_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - sender_recovery_begin);
    std::vector<Address> senders(block.transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        if (recovered_senders[i].has_value()) {
            senders[i] = recovered_senders[i].value();
        }
        else {
            return TransactionError::MissingSender;
        }
    }

    // Call tracer initialization
    std::vector<std::vector<CallFrame>> call_frames{block.transactions.size()};
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers{
        block.transactions.size()};
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers{
        block.transactions.size()};
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        call_tracers[i] =
            enable_tracing
                ? std::unique_ptr<CallTracerBase>{std::make_unique<CallTracer>(
                      block.transactions[i], call_frames[i])}
                : std::unique_ptr<CallTracerBase>{
                      std::make_unique<NoopCallTracer>()};
        state_tracers[i] = std::unique_ptr<trace::StateTracer>{
            std::make_unique<trace::StateTracer>(std::monostate{})};
    }

    // Core execution: transaction-level EVM execution that tracks state
    // changes but does not commit them
    db.set_block_and_prefix(block.header.number - 1, parent_block_id);
    BlockMetrics block_metrics;
    BlockState block_state(db, vm);
    BOOST_OUTCOME_TRY(
        auto const receipts,
        execute_block<traits>(
            chain,
            block,
            senders,
            recovered_authorities,
            block_state,
            block_hash_buffer,
            priority_pool.fiber_group(),
            block_metrics,
            call_tracers,
            state_tracers));

    // Database commit of state changes (incl. Merkle root calculations)
    block_state.log_debug();
    auto const commit_begin = std::chrono::steady_clock::now();
    block_state.commit(
        bytes32_t{block.header.number},
        block.header,
        receipts,
        call_frames,
        senders,
        block.transactions,
        block.ommers,
        block.withdrawals);
    [[maybe_unused]] auto const commit_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - commit_begin);
    if (commit_time > std::chrono::milliseconds(500)) {
        LOG_WARNING(
            "Slow block commit detected - block {}: {}",
            block.header.number,
            commit_time);
    }
    // Post-commit validation of header, with Merkle root fields filled in
    auto const output_header = db.read_eth_header();
    BOOST_OUTCOME_TRY(validate_output_header(block.header, output_header));

    // Commit prologue: database finalization, computation of the Ethereum
    // block hash to append to the circular hash buffer
    db.finalize(block.header.number, block_id);
    db.update_verified_block(block.header.number);
    auto const eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(block.header)));
    block_hash_buffer.set(block.header.number, eth_block_hash);

    return BlockStats{
        .num_retries = block_metrics.num_retries,
        .sender_recovery_time = sender_recovery_time,
        .tx_exec_time = block_metrics.tx_exec_time,
        .commit_time = commit_time,
    };
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &chain, std::filesystem::path const &ledger_dir, Db &db,
    vm::VM &vm, BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop,
    bool const enable_tracing)
{
    uint64_t const batch_size =
        end_block_num == std::numeric_limits<uint64_t>::max() ? 1 : 10000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;
    BatchStats batch_stats{};

    BlockDb block_db(ledger_dir);
    bytes32_t parent_block_id{};
    while (block_num <= end_block_num && stop == 0) {
        Block block;
        MONAD_ASSERT_PRINTF(
            block_db.get(block_num, block),
            "Could not query %lu from blockdb",
            block_num);

        bytes32_t const block_id = bytes32_t{block.header.number};
        evmc_revision const rev =
            chain.get_revision(block.header.number, block.header.timestamp);

        BOOST_OUTCOME_TRY(auto const block_stats, [&]() -> Result<BlockStats> {
            SWITCH_EVM_TRAITS(
                process_ethereum_block,
                chain,
                db,
                vm,
                block_hash_buffer,
                priority_pool,
                block,
                block_id,
                parent_block_id,
                enable_tracing);
            MONAD_ABORT_PRINTF("unhandled rev switch case: %d", rev);
        }());

        ntxs += block.transactions.size();
        batch_num_txs += block.transactions.size();
        total_gas += block.header.gas_used;
        batch_gas += block.header.gas_used;
        ++batch_num_blocks;
        batch_stats.num_retries += block_stats.num_retries;
        batch_stats.sender_recovery_time += block_stats.sender_recovery_time;
        batch_stats.tx_exec_time += block_stats.tx_exec_time;
        batch_stats.commit_time += block_stats.commit_time;

        if (block_num % batch_size == 0) {
            log_tps(
                block_num,
                batch_num_blocks,
                batch_num_txs,
                batch_gas,
                batch_begin,
                batch_stats);
            batch_num_blocks = 0;
            batch_num_txs = 0;
            batch_gas = 0;
            batch_stats = {};
            batch_begin = std::chrono::steady_clock::now();
        }
        parent_block_id = block_id;
        ++block_num;
    }
    if (batch_num_blocks > 0) {
        log_tps(
            block_num,
            batch_num_blocks,
            batch_num_txs,
            batch_gas,
            batch_begin,
            batch_stats);
    }
    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
