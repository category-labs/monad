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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/fiber/fiber_group.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/math.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/ecrecover/impl.hpp>
#include <category/execution/ethereum/core/ecrecover/types.hpp>
#include <category/execution/ethereum/core/fmt/transaction_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/units.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/dispatch_transaction.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_block_header.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/staking/priority_fee.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <quill/std/Optional.h>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <memory>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using namespace monad::literals;

// EIP-4895
void process_withdrawal(
    State &state, std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    if (withdrawals.has_value()) {
        for (auto const &withdrawal : withdrawals.value()) {
            state.add_to_balance(
                withdrawal.recipient, uint256_t{withdrawal.amount} * GWEI);
        }
    }
}

// recover_signers splits the pooled signatures into batches of up to
// MAX_SIGNER_BATCH, aiming for SIGNER_BATCHES_PER_THREAD batches per pool
// thread so the load stays balanced. A batch larger than SIGNER_BATCH_LANES
// is rounded up to a multiple of it, the lane count of a vectorized
// recover_addresses.
constexpr size_t SIGNER_BATCH_LANES = 8;
constexpr size_t MAX_SIGNER_BATCH = 256;
constexpr size_t SIGNER_BATCHES_PER_THREAD = 4;

size_t
signer_batch_size(size_t const num_signatures, unsigned const num_threads)
{
    size_t const target_batches =
        std::max(size_t{1}, size_t{num_threads}) * SIGNER_BATCHES_PER_THREAD;
    size_t const size = std::max(
        size_t{1}, (num_signatures + target_batches - 1) / target_batches);
    if (size <= SIGNER_BATCH_LANES) {
        return size;
    }
    return std::min(MAX_SIGNER_BATCH, round_up(size, SIGNER_BATCH_LANES));
}

// Index of the transaction owning signature `index`, where transaction i owns
// the signatures [offsets[i], offsets[i + 1])
size_t transaction_of_signature(
    std::span<size_t const> const offsets, size_t const index)
{
    MONAD_ASSERT(!offsets.empty() && index < offsets.back());
    return static_cast<size_t>(
               std::ranges::upper_bound(offsets, index) - offsets.begin()) -
           1;
}

// Recovers the signatures [begin, end) of the pooled sequence, in which
// transaction i owns [offsets[i], offsets[i + 1]): first its sender, then its
// authorization entries in order. Every signature has its own element of
// `signers`, so batches over disjoint ranges can run concurrently.
void recover_signer_batch(
    std::span<Transaction const> const transactions,
    std::span<size_t const> const offsets, size_t const begin, size_t const end,
    RecoveredSigners &signers)
{
    std::vector<RecoverAddressInput> inputs;
    std::vector<std::optional<Address> *> results;
    inputs.reserve(end - begin);
    results.reserve(end - begin);

    size_t tx = transaction_of_signature(offsets, begin);
    for (size_t index = begin; index < end; ++index) {
        while (index >= offsets[tx + 1]) {
            ++tx;
        }
        Transaction const &transaction = transactions[tx];
        size_t const slot = index - offsets[tx];
        std::optional<RecoverAddressInput> input;
        std::optional<Address> *result;
        if (slot == 0) {
            input = make_sender_recover_input(transaction);
            result = &signers.senders[tx];
        }
        else {
            input = make_authority_recover_input(
                transaction.authorization_list[slot - 1]);
            result = &signers.authorities[tx][slot - 1];
        }
        // A malformed signature has no signer, so its result stays nullopt
        if (input.has_value()) {
            inputs.push_back(*input);
            results.push_back(result);
        }
    }

    std::vector<RecoverAddressOutput> outputs(inputs.size());
    recover_addresses(inputs, outputs);
    for (size_t i = 0; i < outputs.size(); ++i) {
        *results[i] = to_address(outputs[i]);
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

RecoveredSigners recover_signers(
    std::span<Transaction const> const transactions,
    fiber::PriorityPool &priority_pool)
{
    RecoveredSigners signers{
        .senders = std::vector<std::optional<Address>>(transactions.size()),
        .authorities = {}};
    signers.authorities.reserve(transactions.size());

    // Transaction i owns the signatures [offsets[i], offsets[i + 1]) of the
    // pooled sequence
    std::vector<size_t> offsets;
    offsets.reserve(transactions.size() + 1);
    offsets.push_back(0);
    for (Transaction const &transaction : transactions) {
        size_t const num_authorities = transaction.authorization_list.size();
        signers.authorities.emplace_back(num_authorities);
        offsets.push_back(offsets.back() + 1 + num_authorities);
    }

    size_t const num_signatures = offsets.back();
    if (num_signatures == 0) {
        return signers;
    }
    size_t const batch_size =
        signer_batch_size(num_signatures, priority_pool.num_threads());
    size_t const num_batches = (num_signatures + batch_size - 1) / batch_size;

    // Shared with the tasks, which may still be inside set_value when the
    // waiter below wakes up
    auto const promises =
        std::make_shared<std::vector<boost::fibers::promise<void>>>(
            num_batches);
    std::vector<boost::fibers::future<void>> futures;
    futures.reserve(num_batches);
    for (auto &promise : *promises) {
        futures.push_back(promise.get_future());
    }

    for (size_t batch = 0; batch < num_batches; ++batch) {
        size_t const begin = batch * batch_size;
        size_t const end = std::min(num_signatures, begin + batch_size);
        // Prioritize by the first transaction the batch covers, so batches
        // for earlier transactions are scheduled first
        uint64_t const priority = transaction_of_signature(offsets, begin);
        priority_pool.submit(
            priority,
            [batch,
             begin,
             end,
             promises,
             transactions,
             offsets = std::span<size_t const>{offsets},
             &signers] {
                TRACE_TXN_EVENT(StartSenderRecovery);
                std::exception_ptr current_exception = nullptr;
                try {
                    recover_signer_batch(
                        transactions, offsets, begin, end, signers);
                }
                catch (...) {
                    current_exception = std::current_exception();
                }
                // Signalled outside the catch block, as in
                // execute_block_transactions
                if (MONAD_UNLIKELY(current_exception)) {
                    (*promises)[batch].set_exception(current_exception);
                }
                else {
                    (*promises)[batch].set_value();
                }
            });
    }

    // Every batch writes into `signers` and reads `offsets`, so all of them
    // must finish before an exception from any one is rethrown
    for (auto const &future : futures) {
        future.wait();
    }
    for (auto &future : futures) {
        future.get();
    }

    return signers;
}

template <Traits traits>
Result<std::vector<Receipt>> execute_block_transactions(
    Chain const &chain, BlockHeader const &header,
    std::span<Transaction const> const transactions,
    std::span<Address const> const senders,
    std::span<std::vector<std::optional<Address>> const> const authorities,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::FiberGroup &priority_pool, BlockMetrics &block_metrics,
    std::span<std::unique_ptr<CallTracerBase>> const call_tracers,
    std::span<std::unique_ptr<trace::StateTracer>> const state_tracers,
    ChainContext<traits> const &chain_ctx,
    ExecutionEventRecorder *const exec_recorder, bool const trace_transfers)
{
    MONAD_ASSERT(senders.size() == transactions.size());
    MONAD_ASSERT(senders.size() == call_tracers.size());
    MONAD_ASSERT(senders.size() == state_tracers.size());

    std::shared_ptr<boost::fibers::promise<void>[]> const promises{
        new boost::fibers::promise<void>[transactions.size() + 1]};
    std::shared_ptr<boost::fibers::future<void>[]> const futures{
        new boost::fibers::future<void>[transactions.size() + 1]};
    for (auto i = 0u; i < transactions.size() + 1; ++i) {
        futures[i] = promises[i].get_future();
    }
    promises[0].set_value();

    std::shared_ptr<std::optional<Result<Receipt>>[]> const results{
        new std::optional<Result<Receipt>>[transactions.size()]};
    size_t const txn_count = transactions.size();

    auto const tx_exec_begin = std::chrono::steady_clock::now();
    for (unsigned i = 0; i < txn_count; ++i) {
        priority_pool.submit(
            i,
            [&chain = chain,
             i = i,
             results = results,
             promises = promises,
             futures = futures,
             &transaction = transactions[i],
             &sender = senders[i],
             &authorities = authorities[i],
             &header = header,
             &block_hash_buffer = block_hash_buffer,
             &block_state,
             &block_metrics,
             &call_tracer = *call_tracers[i],
             &state_tracer = *state_tracers[i],
             &chain_ctx = chain_ctx,
             exec_recorder = exec_recorder,
             trace_transfers = trace_transfers] {
                record_txn_marker_event(
                    exec_recorder, MONAD_EXEC_TXN_PERF_EVM_ENTER, i);
                std::exception_ptr current_exception = nullptr;
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
                        futures[i],
                        call_tracer,
                        state_tracer,
                        chain_ctx,
                        exec_recorder,
                        trace_transfers);
                    if (results[i]->has_error()) {
                        record_txn_error_event(
                            exec_recorder, i, results[i]->error());
                    }
                    record_txn_marker_event(
                        exec_recorder, MONAD_EXEC_TXN_PERF_EVM_EXIT, i);
                }
                catch (...) {
                    current_exception = std::current_exception();
                }

                // Call `promises[i + 1].set_{exception,value}` as the last
                // thing, signalling that this transaction has finished.
                if (MONAD_UNLIKELY(current_exception)) {
                    // An exception occurred during the execution of this
                    // transaction. We must wait on the predecessor transaction
                    // here to maintain the invariant that execution of every
                    // transaction has finished before processing the results.
                    // We wait here rather than inside the catch block, because
                    // Boost Fiber does not support suspending within an
                    // exception handler.
                    futures[i].wait();
                    promises[i + 1].set_exception(current_exception);
                }
                else {
                    promises[i + 1].set_value();
                }
            });
    }

    auto const last = static_cast<ptrdiff_t>(transactions.size());
    futures[last].wait();
    for (ptrdiff_t i = 1; i <= last; ++i) {
        futures[i].get();
    }
    block_metrics.tx_exec_time =
        std::chrono::duration_cast<std::chrono::microseconds>(
            std::chrono::steady_clock::now() - tx_exec_begin);

    std::vector<Receipt> retvals;
    for (unsigned i = 0; i < transactions.size(); ++i) {
        MONAD_ASSERT_THROW(
            results[i].has_value(), "missing transaction result");
        auto &result = results[i].value();
        if (MONAD_UNLIKELY(result.has_error())) {
            LOG_ERROR(
                "tx {} {} validation failed: {}",
                i,
                transactions[i],
                result.assume_error().message().c_str());
            return std::move(result).as_failure();
        }
        retvals.push_back(std::move(result).assume_value());
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &receipt : retvals) {
        cumulative_gas_used += receipt.gas_used;
        receipt.gas_used = cumulative_gas_used;
    }

    return retvals;
}

template <Traits traits>
Result<std::vector<Receipt>> execute_block(
    Chain const &chain, Block const &block,
    std::span<Address const> const senders,
    std::span<std::vector<std::optional<Address>> const> const authorities,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::FiberGroup &priority_pool, BlockMetrics &block_metrics,
    std::span<std::unique_ptr<CallTracerBase>> const call_tracers,
    std::span<std::unique_ptr<trace::StateTracer>> const state_tracers,
    trace::StateTracer &system_call_state_tracer,
    ChainContext<traits> const &chain_ctx,
    ExecutionEventRecorder *const exec_recorder, bool const trace_transfers)
{
    static_assert(traits::evm_rev() >= EvmRevision::SpuriousDragon);

    TRACE_BLOCK_EVENT(StartBlock);

    MONAD_ASSERT(senders.size() == block.transactions.size());
    MONAD_ASSERT(senders.size() == call_tracers.size());
    MONAD_ASSERT(senders.size() == state_tracers.size());

    execute_block_header<traits>(block_state, block.header, exec_recorder);

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
            state_tracers,
            chain_ctx,
            exec_recorder,
            trace_transfers));

    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (traits::eip_4895_active()) {
        process_withdrawal(state, block.withdrawals);
    }

    if constexpr (traits::eip_7685_active()) {
        MONAD_ASSERT_THROW(
            block.header.requests_hash.has_value(),
            "block header must have requests hash when EIP-7685 is active");
        BOOST_OUTCOME_TRY(
            auto const computed_requests_hash,
            process_requests<traits>(
                chain,
                state,
                block_hash_buffer,
                block.header,
                system_call_state_tracer,
                chain_ctx,
                retvals));
        if (MONAD_UNLIKELY(
                computed_requests_hash != block.header.requests_hash.value())) {
            return BlockError::InvalidRequestsHash;
        }
    }

    if constexpr (traits::eip_7928_active()) {
        MONAD_ASSERT_THROW(
            block.header.block_access_list_hash.has_value(),
            "block header must have block access list hash when EIP-7928 is "
            "active");
        // TODO(EIP-7928) compute and validate hash
    }

    apply_block_reward<traits>(state, block);

    // TODO: move to execute_monad_block
    if constexpr (traits::mip_11_active()) {
        staking::distribute_priority_fees(state);
    }

    state.destruct_touched_dead();

    MONAD_ASSERT_THROW(
        block_state.can_merge(state), "block state cannot be merged");
    block_state.merge(state);
    record_account_access_events(
        exec_recorder, MONAD_ACCT_ACCESS_BLOCK_EPILOGUE, state);

    return retvals;
}

// Explicit instantiations using EXPLICIT_TRAITS macro
EXPLICIT_TRAITS(execute_block_transactions);
EXPLICIT_TRAITS(execute_block);

MONAD_NAMESPACE_END
