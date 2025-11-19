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

#include "runloop_monad_ethblocks.hpp"

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/core/procfs/statm.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
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
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/validate_monad_block.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <boost/outcome/try.hpp>
#include <quill/Quill.h>

#include <algorithm>
#include <chrono>
#include <memory>
#include <optional>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

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
            std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
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

// Process a single Monad block stored in Ethereum format
template <Traits traits>
Result<void> process_monad_block(
    MonadChain const &chain, Db &db, vm::VM &vm,
    BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, Block &block, bytes32_t const &block_id,
    bytes32_t const &parent_block_id, bool const enable_tracing,
    ankerl::unordered_dense::segmented_set<Address> const
        *grandparent_senders_and_authorities,
    ankerl::unordered_dense::segmented_set<Address> const
        *parent_senders_and_authorities,
    ankerl::unordered_dense::segmented_set<Address>
        &senders_and_authorities_out)
{
    [[maybe_unused]] auto const block_start = std::chrono::system_clock::now();
    auto const block_begin = std::chrono::steady_clock::now();

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
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
    for (Address const &sender : senders) {
        senders_and_authorities.insert(sender);
    }
    for (std::vector<std::optional<Address>> const &authorities :
         recovered_authorities) {
        for (std::optional<Address> const &authority : authorities) {
            if (authority.has_value()) {
                senders_and_authorities.insert(authority.value());
            }
        }
    }
    BOOST_OUTCOME_TRY(
        static_validate_monad_body<traits>(senders, block.transactions));

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

    senders_and_authorities_out = senders_and_authorities;

    MonadChainContext chain_context{
        .grandparent_senders_and_authorities =
            grandparent_senders_and_authorities,
        .parent_senders_and_authorities = parent_senders_and_authorities,
        .senders_and_authorities = senders_and_authorities,
        .senders = senders,
        .authorities = recovered_authorities};

    // Core execution: transaction-level EVM execution that tracks state
    // changes but does not commit them
    db.set_block_and_prefix(block.header.number - 1, parent_block_id);
    block.header.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(db.read_eth_header())));

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
            state_tracers,
            [&chain, &block, &chain_context](
                Address const &sender,
                Transaction const &tx,
                uint64_t const i,
                State &state) {
                return chain.revert_transaction(
                    block.header.number,
                    block.header.timestamp,
                    sender,
                    tx,
                    block.header.base_fee_per_gas.value_or(0),
                    i,
                    state,
                    chain_context);
            }));

    // Database commit of state changes (incl. Merkle root calculations)
    block_state.log_debug();
    auto const commit_begin = std::chrono::steady_clock::now();
    block_state.commit(
        block_id,
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
    BOOST_OUTCOME_TRY(
        chain.validate_output_header(block.header, output_header));

    // Commit prologue: database finalization, computation of the Ethereum
    // block hash to append to the circular hash buffer
    db.finalize(block.header.number, block_id);
    db.update_verified_block(block.header.number);
    auto const eth_block_hash =
        to_bytes(keccak256(rlp::encode_block_header(output_header)));
    block_hash_buffer.set(block.header.number, eth_block_hash);

    // Emit the block metrics log line
    [[maybe_unused]] auto const block_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - block_begin);
    LOG_INFO(
        "__exec_block,bl={:8},ts={}"
        ",tx={:5},rt={:4},rtp={:5.2f}%"
        ",sr={:>7},txe={:>8},cmt={:>8},tot={:>8},tpse={:5},tps={:5}"
        ",gas={:9},gpse={:4},gps={:3}{}{}{}",
        block.header.number,
        std::chrono::duration_cast<std::chrono::milliseconds>(
            block_start.time_since_epoch())
            .count(),
        block.transactions.size(),
        block_metrics.num_retries(),
        100.0 * (double)block_metrics.num_retries() /
            std::max(1.0, (double)block.transactions.size()),
        sender_recovery_time,
        block_metrics.tx_exec_time(),
        commit_time,
        block_time,
        block.transactions.size() * 1'000'000 /
            (uint64_t)std::max(1L, block_metrics.tx_exec_time().count()),
        block.transactions.size() * 1'000'000 /
            (uint64_t)std::max(1L, block_time.count()),
        output_header.gas_used,
        output_header.gas_used /
            (uint64_t)std::max(1L, block_metrics.tx_exec_time().count()),
        output_header.gas_used / (uint64_t)std::max(1L, block_time.count()),
        db.print_stats(),
        vm.print_and_reset_block_counts(),
        vm.print_compiler_stats());

    return outcome_e::success();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::pair<uint64_t, uint64_t>> runloop_monad_ethblocks(
    MonadChain const &chain, std::filesystem::path const &ledger_dir, Db &db,
    vm::VM &vm, BlockHashBufferFinalized &block_hash_buffer,
    fiber::PriorityPool &priority_pool, uint64_t &finalized_block_num,
    uint64_t const end_block_num, sig_atomic_t const volatile &stop,
    bool const enable_tracing)
{
    uint64_t const batch_size =
        end_block_num == std::numeric_limits<uint64_t>::max() ? 1 : 1000;
    uint64_t batch_num_blocks = 0;
    uint64_t batch_num_txs = 0;
    uint64_t total_gas = 0;
    uint64_t batch_gas = 0;
    auto batch_begin = std::chrono::steady_clock::now();
    uint64_t ntxs = 0;

    BlockDb block_db(ledger_dir);
    bytes32_t parent_block_id{};
    uint64_t block_num = finalized_block_num;

    std::optional<ankerl::unordered_dense::segmented_set<Address>>
        parent_senders_and_authorities;
    std::optional<ankerl::unordered_dense::segmented_set<Address>>
        grandparent_senders_and_authorities;

    if (block_num > 1) {
        Block parent_block;
        MONAD_ASSERT_PRINTF(
            block_db.get(block_num - 1, parent_block),
            "Could not query %lu from blockdb for parent",
            block_num - 1);
        auto const recovered_senders =
            recover_senders(parent_block.transactions, priority_pool);
        auto const recovered_authorities =
            recover_authorities(parent_block.transactions, priority_pool);
        std::vector<Address> senders(parent_block.transactions.size());
        for (unsigned j = 0; j < recovered_senders.size(); ++j) {
            if (recovered_senders[j].has_value()) {
                senders[j] = recovered_senders[j].value();
            }
        }
        ankerl::unordered_dense::segmented_set<Address> parent_set;
        for (Address const &sender : senders) {
            parent_set.insert(sender);
        }
        for (std::vector<std::optional<Address>> const &authorities :
             recovered_authorities) {
            for (std::optional<Address> const &authority : authorities) {
                if (authority.has_value()) {
                    parent_set.insert(authority.value());
                }
            }
        }
        parent_senders_and_authorities = std::move(parent_set);

        if (block_num > 2) {
            Block grandparent_block;
            MONAD_ASSERT_PRINTF(
                block_db.get(block_num - 2, grandparent_block),
                "Could not query %lu from blockdb for grandparent",
                block_num - 2);
            auto const grandparent_recovered_senders =
                recover_senders(grandparent_block.transactions, priority_pool);
            auto const grandparent_recovered_authorities = recover_authorities(
                grandparent_block.transactions, priority_pool);
            std::vector<Address> grandparent_senders(
                grandparent_block.transactions.size());
            for (unsigned j = 0; j < grandparent_recovered_senders.size();
                 ++j) {
                if (grandparent_recovered_senders[j].has_value()) {
                    grandparent_senders[j] =
                        grandparent_recovered_senders[j].value();
                }
            }
            ankerl::unordered_dense::segmented_set<Address> grandparent_set;
            for (Address const &sender : grandparent_senders) {
                grandparent_set.insert(sender);
            }
            for (std::vector<std::optional<Address>> const &authorities :
                 grandparent_recovered_authorities) {
                for (std::optional<Address> const &authority : authorities) {
                    if (authority.has_value()) {
                        grandparent_set.insert(authority.value());
                    }
                }
            }
            grandparent_senders_and_authorities = std::move(grandparent_set);
        }
    }

    while (block_num <= end_block_num && stop == 0) {
        Block block;
        MONAD_ASSERT_PRINTF(
            block_db.get(block_num, block),
            "Could not query %lu from blockdb",
            block_num);

        bytes32_t const block_id = bytes32_t{block.header.number};
        monad_revision const rev =
            chain.get_monad_revision(block.header.timestamp);

        ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
        BOOST_OUTCOME_TRY([&] {
            SWITCH_MONAD_TRAITS(
                process_monad_block,
                chain,
                db,
                vm,
                block_hash_buffer,
                priority_pool,
                block,
                block_id,
                parent_block_id,
                enable_tracing,
                grandparent_senders_and_authorities.has_value()
                    ? &grandparent_senders_and_authorities.value()
                    : nullptr,
                parent_senders_and_authorities.has_value()
                    ? &parent_senders_and_authorities.value()
                    : nullptr,
                senders_and_authorities);
            MONAD_ABORT_PRINTF("unhandled rev switch case: %d", rev);
        }());

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

        grandparent_senders_and_authorities =
            std::move(parent_senders_and_authorities);
        parent_senders_and_authorities = std::move(senders_and_authorities);

        parent_block_id = block_id;
        ++block_num;
    }
    if (batch_num_blocks > 0) {
        log_tps(
            block_num, batch_num_blocks, batch_num_txs, batch_gas, batch_begin);
    }
    finalized_block_num = block_num;
    return {ntxs, total_gas};
}

MONAD_NAMESPACE_END
