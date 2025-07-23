#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/cpu_relax.h>
#include <category/core/event/event_recorder.h>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/eth_ctypes.h>
#include <category/execution/ethereum/core/fmt/transaction_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/dao.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/explicit_evmc_revision.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/switch_evmc_revision.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/ethereum/validate_block.hpp>

#include <evmc/evmc.h>
#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <span>
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

void transfer_balance_dao(State &prologue_state)
{
    for (auto const &addr : dao::child_accounts) {
        auto const balance =
            intx::be::load<uint256_t>(prologue_state.get_balance(addr));
        prologue_state.add_to_balance(dao::withdraw_account, balance);
        prologue_state.subtract_from_balance(addr, balance);
    }
}

// EIP-4788
void set_beacon_root(State &prologue_state, BlockHeader const &header)
{
    constexpr auto BEACON_ROOTS_ADDRESS{
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02_address};
    constexpr uint256_t HISTORY_BUFFER_LENGTH{8191};

    if (prologue_state.account_exists(BEACON_ROOTS_ADDRESS)) {
        uint256_t timestamp{header.timestamp};
        bytes32_t k1{
            to_bytes(to_big_endian(timestamp % HISTORY_BUFFER_LENGTH))};
        bytes32_t k2{to_bytes(to_big_endian(
            timestamp % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH))};
        prologue_state.set_storage(
            BEACON_ROOTS_ADDRESS, k1, to_bytes(to_big_endian(timestamp)));
        prologue_state.set_storage(
            BEACON_ROOTS_ADDRESS, k2, header.parent_beacon_block_root.value());
    }
}

// EIP-2935
void set_block_hash_history(State &prologue_state, BlockHeader const &header)
{
    constexpr auto HISTORY_STORAGE_ADDRESS{
        0x0000F90827F1C53a10cb7A02335B175320002935_address};
    constexpr uint256_t HISTORY_SERVE_WINDOW{8191};

    if (prologue_state.account_exists(HISTORY_STORAGE_ADDRESS)) {
        uint256_t const block_number{header.number};
        bytes32_t const key{
            to_bytes(to_big_endian((block_number - 1) % HISTORY_SERVE_WINDOW))};
        prologue_state.set_storage(
            HISTORY_STORAGE_ADDRESS, key, header.parent_hash);
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::vector<std::optional<Address>> recover_senders(
    std::vector<Transaction> const &transactions,
    fiber::PriorityPool &priority_pool)
{
    std::vector<std::optional<Address>> senders{transactions.size()};
    std::atomic<std::size_t> recovered_count = 0;
    size_t const txn_count = transactions.size();

    for (unsigned i = 0; i < txn_count; ++i) {
        priority_pool.submit(
            i,
            [&sender = senders[i],
             &transaction = transactions[i],
             &recovered_count] {
                sender = recover_sender(transaction);
                recovered_count.fetch_add(1, std::memory_order_relaxed);
            });
    }

    while (recovered_count.load(std::memory_order_relaxed) < txn_count) {
        cpu_relax();
    }

    return senders;
}

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &chain, Block &block, std::vector<Address> const &senders,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool, BlockMetrics &block_metrics)
{
    TRACE_BLOCK_EVENT(StartBlock);

    MONAD_ASSERT(senders.size() == block.transactions.size());

    // A few "system level" state-affecting operations occur prior to
    // transaction execution.
    State prologue_state{block_state, Incarnation{block.header.number, 0}};

    if constexpr (rev >= EVMC_PRAGUE) {
        set_block_hash_history(prologue_state, block.header);
    }

    if constexpr (rev >= EVMC_CANCUN) {
        set_beacon_root(prologue_state, block.header);
    }

    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
            transfer_balance_dao(prologue_state);
        }
    }

    MONAD_ASSERT(block_state.can_merge(prologue_state));
    block_state.merge(prologue_state);
    record_account_access_events(
        MONAD_ACCT_ACCESS_BLOCK_PROLOGUE, prologue_state);

    std::shared_ptr<boost::fibers::promise<void>[]> promises{
        new boost::fibers::promise<void>[block.transactions.size() + 1]};
    promises[0].set_value();

    std::shared_ptr<std::optional<Result<ExecutionResult>>[]> const results{
        new std::optional<Result<ExecutionResult>>[block.transactions.size()]};
    std::atomic<size_t> txn_exec_finished = 0;
    size_t const txn_count = block.transactions.size();

    auto const tx_exec_begin = std::chrono::steady_clock::now();
    for (unsigned i = 0; i < txn_count; ++i) {
        priority_pool.submit(
            i,
            [&chain = chain,
             i = i,
             txn_count = txn_count,
             results = results,
             promises = promises,
             &transaction = block.transactions[i],
             &sender = senders[i],
             &header = block.header,
             &block_hash_buffer = block_hash_buffer,
             &block_state,
             &block_metrics,
             &txn_exec_finished] {
                record_exec_event(i, MONAD_EXEC_TXN_PERF_EVM_ENTER);
                results[i].emplace(execute<rev>(
                    chain,
                    i,
                    transaction,
                    sender,
                    header,
                    block_hash_buffer,
                    block_state,
                    block_metrics,
                    promises[i]));
                promises[i + 1].set_value();
                record_exec_event(i, MONAD_EXEC_TXN_PERF_EVM_EXIT);

                // Epilogue: demote the priority of the recording
                // operation and yield the thread to a more important fiber
                boost::this_fiber::properties<fiber::PriorityProperties>()
                    .set_priority(txn_count + i);
                boost::this_fiber::yield();
                record_txn_events(i, transaction, sender, *results[i]);
                txn_exec_finished.fetch_add(1, std::memory_order::relaxed);
            });
    }

    auto const last = static_cast<std::ptrdiff_t>(block.transactions.size());
    promises[last].get_future().wait();
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

    std::vector<ExecutionResult> retvals;
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        MONAD_ASSERT(results[i].has_value());
        if (MONAD_UNLIKELY(results[i].value().has_error())) {
            LOG_ERROR(
                "tx {} {} validation failed: {}",
                i,
                block.transactions[i],
                results[i].value().assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto retval, std::move(results[i].value()));
        retvals.push_back(std::move(retval));
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &[_, receipt, call_frame] : retvals) {
        cumulative_gas_used += receipt.gas_used;
        receipt.gas_used = cumulative_gas_used;
    }

    State epilogue_state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (rev >= EVMC_SHANGHAI) {
        process_withdrawal(epilogue_state, block.withdrawals);
    }

    apply_block_reward<rev>(epilogue_state, block);

    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        epilogue_state.destruct_touched_dead();
    }

    MONAD_ASSERT(block_state.can_merge(epilogue_state));
    block_state.merge(epilogue_state);
    record_account_access_events(
        MONAD_ACCT_ACCESS_BLOCK_EPILOGUE, epilogue_state);

    return retvals;
}

EXPLICIT_EVMC_REVISION(execute_block);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &chain, evmc_revision const rev, Block &block,
    std::vector<Address> const &senders, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool, BlockMetrics &block_metrics)
{
    SWITCH_EVMC_REVISION(
        execute_block,
        chain,
        block,
        senders,
        block_state,
        block_hash_buffer,
        priority_pool,
        block_metrics);
    MONAD_ABORT_PRINTF(
        "unhandled evmc revision %u", static_cast<unsigned>(rev));
}

MONAD_NAMESPACE_END
