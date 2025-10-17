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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/cpu_relax.h>
#include <category/core/event/event_recorder.h>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/transaction_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/dao.hpp>
#include <category/execution/ethereum/dispatch_transaction.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <evmc/evmc.h>
#include <intx/intx.hpp>

#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// EIP-4895
void process_withdrawal(
    State &state, std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    if (withdrawals.has_value()) {
        for (auto const &withdrawal : withdrawals.value()) {
            state.add_to_balance(
                withdrawal.recipient,
                uint256_t{withdrawal.amount} * uint256_t{1'000'000'000u});
        }
    }
}

void transfer_balance_dao(State &state)
{
    for (auto const &addr : dao::child_accounts) {
        auto const balance = intx::be::load<uint256_t>(state.get_balance(addr));
        state.add_to_balance(dao::withdraw_account, balance);
        state.subtract_from_balance(addr, balance);
    }
}

// EIP-4788
void set_beacon_root(State &state, BlockHeader const &header)
{
    constexpr auto BEACON_ROOTS_ADDRESS{
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02_address};
    constexpr uint256_t HISTORY_BUFFER_LENGTH{8191};

    if (state.account_exists(BEACON_ROOTS_ADDRESS)) {
        uint256_t timestamp{header.timestamp};
        bytes32_t k1{
            to_bytes(to_big_endian(timestamp % HISTORY_BUFFER_LENGTH))};
        bytes32_t k2{to_bytes(to_big_endian(
            timestamp % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH))};
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k1, to_bytes(to_big_endian(timestamp)));
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k2, header.parent_beacon_block_root.value());
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::vector<std::optional<Address>> recover_senders(
    std::vector<Transaction> const &transactions,
    fiber::PriorityPool &priority_pool)
{
    std::vector<std::optional<Address>> senders{transactions.size()};

    std::shared_ptr<boost::fibers::promise<void>[]> promises{
        new boost::fibers::promise<void>[transactions.size()]};

    for (unsigned i = 0; i < transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [i = i,
             promises = promises,
             &sender = senders[i],
             &transaction = transactions[i]] {
                sender = recover_sender(transaction);
                promises[i].set_value();
            });
    }

    for (unsigned i = 0; i < transactions.size(); ++i) {
        promises[i].get_future().wait();
    }

    return senders;
}

std::vector<std::vector<std::optional<Address>>> recover_authorities(
    std::vector<Transaction> const &transactions,
    fiber::PriorityPool &priority_pool)
{
    std::vector<std::vector<std::optional<Address>>> authorities{
        transactions.size()};
    std::vector<std::shared_ptr<boost::fibers::promise<void>[]>> promises{
        transactions.size()};

    for (auto i = 0u; i < transactions.size(); ++i) {
        authorities[i] = std::vector<std::optional<Address>>{
            transactions[i].authorization_list.size()};
        promises[i] = std::shared_ptr<boost::fibers::promise<void>[]>{
            new boost::fibers::promise<void>[authorities[i].size()]};

        for (auto j = 0u; j < authorities[i].size(); ++j) {
            priority_pool.submit(
                i,
                [j = j,
                 auth_promises = promises[i],
                 &auth = authorities[i][j],
                 &auth_entry = transactions[i].authorization_list[j]]() {
                    auth = recover_authority(auth_entry);
                    auth_promises[j].set_value();
                });
        }
    }

    for (auto i = 0u; i < transactions.size(); ++i) {
        for (auto j = 0u; j < transactions[i].authorization_list.size(); ++j) {
            promises[i][j].get_future().wait();
        }
    }

    return authorities;
}

template <Traits traits>
Result<std::vector<Receipt>> execute_block_transactions(
    Chain const &chain, BlockHeader const &header,
    std::vector<Transaction> const &transactions,
    std::vector<Address> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool, BlockMetrics &block_metrics,
    std::vector<std::unique_ptr<CallTracerBase>> &call_tracers,
    RevertTransactionFn const &revert_transaction)
{
    MONAD_ASSERT(senders.size() == transactions.size());
    MONAD_ASSERT(senders.size() == call_tracers.size());

    std::shared_ptr<boost::fibers::promise<void>[]> promises{
        new boost::fibers::promise<void>[transactions.size() + 1]};
    promises[0].set_value();

    std::shared_ptr<std::optional<Result<Receipt>>[]> const results{
        new std::optional<Result<Receipt>>[transactions.size()]};
    std::atomic<size_t> txn_exec_finished = 0;
    size_t const txn_count = transactions.size();

    auto const tx_exec_begin = std::chrono::steady_clock::now();
    for (unsigned i = 0; i < txn_count; ++i) {
        priority_pool.submit(
            i,
            [&chain = chain,
             i = i,
             results = results,
             promises = promises,
             &transaction = transactions[i],
             &sender = senders[i],
             &authorities = authorities[i],
             &header = header,
             &block_hash_buffer = block_hash_buffer,
             &block_state,
             &block_metrics,
             &call_tracer = *call_tracers[i],
             &txn_exec_finished,
             &revert_transaction = revert_transaction] {
                record_txn_marker_event(MONAD_EXEC_TXN_PERF_EVM_ENTER, i);
                try {
                    results[i] = dispatch_transaction<traits>(
                        chain,
                        i,
                        transaction,
                        sender,
                        authorities,
                        header,
                        block_hash_buffer,
                        block_state,
                        block_metrics,
                        promises[i],
                        call_tracer,
                        revert_transaction);
                    promises[i + 1].set_value();
                    record_txn_marker_event(MONAD_EXEC_TXN_PERF_EVM_EXIT, i);
                    record_txn_events(
                        i,
                        transaction,
                        sender,
                        authorities,
                        *results[i],
                        call_tracer.get_call_frames());
                }
                catch (...) {
                    promises[i + 1].set_exception(std::current_exception());
                }
                txn_exec_finished.fetch_add(1, std::memory_order::relaxed);
            });
    }

    auto const last = static_cast<std::ptrdiff_t>(transactions.size());
    promises[last].get_future().get();
    block_metrics.set_tx_exec_time(
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - tx_exec_begin));

    // All transactions have released their merge-order synchronization
    // primitive (promises[i + 1]) but some stragglers could still be running
    // post-execution code that occurs immediately after that, e.g.
    // `record_txn_exec_result_events`. This waits for everything to finish
    // so that it's safe to assume we're the only ones using `results`.
    while (txn_exec_finished.load() < txn_count) {
        cpu_relax();
    }

    std::vector<Receipt> retvals;
    for (unsigned i = 0; i < transactions.size(); ++i) {
        MONAD_ASSERT(results[i].has_value());
        if (MONAD_UNLIKELY(results[i].value().has_error())) {
            LOG_ERROR(
                "tx {} {} validation failed: {}",
                i,
                transactions[i],
                results[i].value().assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto retval, std::move(results[i].value()));
        retvals.push_back(std::move(retval));
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &receipt : retvals) {
        cumulative_gas_used += receipt.gas_used;
        receipt.gas_used = cumulative_gas_used;
    }

    return retvals;
}

EXPLICIT_TRAITS(execute_block_transactions);

template <Traits traits>
Result<std::vector<Receipt>> execute_block(
    Chain const &chain, Block const &block, std::vector<Address> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool, BlockMetrics &block_metrics,
    std::vector<std::unique_ptr<CallTracerBase>> &call_tracers,
    RevertTransactionFn const &revert_transaction)
{
    TRACE_BLOCK_EVENT(StartBlock);

    MONAD_ASSERT(senders.size() == block.transactions.size());
    MONAD_ASSERT(senders.size() == call_tracers.size());

    {
        State state{block_state, Incarnation{block.header.number, 0}};

        if constexpr (traits::evm_rev() >= EVMC_PRAGUE) {
            deploy_block_hash_history_contract(state);
        }

        set_block_hash_history(state, block.header);

        if constexpr (traits::evm_rev() >= EVMC_CANCUN) {
            set_beacon_root(state, block.header);
        }

        // Ethereum mainnet dao fork
        if constexpr (traits::evm_rev() == EVMC_HOMESTEAD) {
            if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
                if (chain.get_chain_id() == 1) {
                    transfer_balance_dao(state);
                }
            }
        }

        MONAD_ASSERT(block_state.can_merge(state));
        state.log_debug();
        block_state.merge(state);
    }

    BOOST_OUTCOME_TRY(
        auto const retvals,
        execute_block_transactions<traits>(
            chain,
            block.header,
            block.transactions,
            senders,
            authorities,
            block_state,
            block_hash_buffer,
            priority_pool,
            block_metrics,
            call_tracers,
            revert_transaction));

    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (traits::evm_rev() >= EVMC_SHANGHAI) {
        process_withdrawal(state, block.withdrawals);
    }

    apply_block_reward<traits>(state, block);

    if constexpr (traits::evm_rev() >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    MONAD_ASSERT(block_state.can_merge(state));
    state.log_debug();
    block_state.merge(state);

    return retvals;
}

EXPLICIT_TRAITS(execute_block);

MONAD_NAMESPACE_END
