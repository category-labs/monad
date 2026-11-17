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
#include <category/core/int.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/staking/priority_fee.hpp>
#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/fiber/future/future.hpp>
#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
ExecuteTransaction<traits>::ExecuteTransaction(
    Chain const &chain, uint64_t const i, Transaction const &tx,
    Address const &sender,
    std::span<std::optional<Address> const> const authorities,
    BlockHeader const &header, BlockHashBuffer const &block_hash_buffer,
    BlockState &block_state, BlockMetrics &block_metrics,
    boost::fibers::future<void> &prev, CallTracerBase &call_tracer,
    trace::StateTracer &state_tracer, ChainContext<traits> const &chain_ctx,
    ExecutionEventRecorder *const exec_recorder, bool const trace_transfers)
    : ExecuteTransactionNoValidation<
          traits>{chain, tx, sender, authorities, header}
    , i_{i}
    , chain_ctx_{chain_ctx}
    , block_hash_buffer_{block_hash_buffer}
    , block_state_{block_state}
    , block_metrics_{block_metrics}
    , prev_{prev}
    , call_tracer_{call_tracer}
    , state_tracer_{state_tracer}
    , exec_recorder_{exec_recorder}
    , trace_transfers_{trace_transfers}
{
    record_txn_header_events(
        exec_recorder_, static_cast<uint32_t>(i), tx, sender, authorities);
}

template <Traits traits>
Result<vm::Result> ExecuteTransaction<traits>::execute_impl2(State &state)
{
    auto validation = validate_transaction<traits>(
        tx_,
        sender_,
        state,
        header_.base_fee_per_gas.value_or(0),
        authorities_,
        state_tracer_,
        chain_ctx_.mode);
    if (!validation) {
        // RELAXED MERGE
        // if transaction validation fails using current values, require
        // exact match during merge as a precaution
        state.original_account_state(sender_).set_validate_exact_balance();
        return std::move(validation).as_failure();
    }

    auto const tx_context = get_tx_context<traits>(
        tx_,
        sender_,
        header_,
        chain_.get_chain_id(),
        chain_.get_blob_schedule(header_.timestamp));
    StateHost<traits> host{
        call_tracer_,
        state_tracer_,
        tx_context,
        block_hash_buffer_,
        state,
        tx_,
        header_.base_fee_per_gas,
        i_,
        chain_ctx_,
        trace_transfers_};

    return ExecuteTransactionNoValidation<traits>::operator()(state, host);
}

template <Traits traits>
Receipt ExecuteTransaction<traits>::execute_final(
    State &state, vm::Result const &result)
{
    static_assert(traits::evm_rev() >= EvmRevision::SpuriousDragon);

    MONAD_ASSERT(result.gas_left >= 0);
    MONAD_ASSERT(result.gas_refund >= 0);
    MONAD_ASSERT(tx_.gas_limit >= static_cast<uint64_t>(result.gas_left));

    // refund and priority, Eqn. 73-76
    // Monad specification §4.2: Storage Gas Cost and Refunds
    auto const gas_refund = compute_gas_refund<traits>(
        tx_,
        static_cast<uint64_t>(result.gas_left),
        static_cast<uint64_t>(result.gas_refund));
    auto const gas_cost =
        gas_price<traits>(tx_, header_.base_fee_per_gas.value_or(0));
    state.add_to_balance(sender_, gas_cost * gas_refund);

    auto gas_used = tx_.gas_limit - gas_refund;

    if constexpr (traits::eip_7623_active()) {
        auto const floor_gas = floor_data_gas<traits>(tx_);
        if (gas_used < floor_gas) {
            auto const delta = floor_gas - gas_used;
            state.subtract_from_balance(sender_, gas_cost * delta);

            gas_used = floor_gas;
        }
    }

    uint256_t const reward = calculate_txn_award<traits>(
        tx_, header_.base_fee_per_gas.value_or(0), gas_used);
    if constexpr (traits::mip_11_active()) {
        staking::collect_priority_fee(state, reward);
    }
    else {
        state.add_to_balance(header_.beneficiary, reward);
    }

    // finalize state, Eqn. 77-79
    state.destruct_suicides<traits>();
    state.destruct_touched_dead();

    Receipt receipt{
        .status = result.status_code == CallStatus::Success ? 1u : 0u,
        .gas_used = gas_used,
        .type = tx_.type};
    for (auto const &log : state.logs()) {
        receipt.add_log(log);
    }

    call_tracer_.on_finish(receipt.gas_used);
    trace::run_tracer<traits>(state_tracer_, state);
    record_txn_output_events(
        exec_recorder_,
        static_cast<uint32_t>(this->i_),
        receipt,
        call_tracer_.get_call_frames(),
        state);

    return receipt;
}

template <Traits traits>
Result<Receipt> ExecuteTransaction<traits>::operator()()
{
    TRACE_TXN_EVENT(StartTxn);

    {
        auto validation_result = static_validate_transaction<traits>(
            tx_,
            header_.base_fee_per_gas,
            header_.excess_blob_gas,
            chain_.get_chain_id(),
            chain_.get_blob_schedule(header_.timestamp));
        if (validation_result.has_error()) {
            prev_.wait();
            return std::move(validation_result).as_failure();
        }
    }

    {
        TRACE_TXN_EVENT(StartExecution);

        State state{block_state_, Incarnation{header_.number, i_ + 1}};
        state.set_original_nonce(sender_, tx_.nonce);

        call_tracer_.reset();
        trace::reset(state_tracer_);

        auto result = execute_impl2(state);

        {
            TRACE_TXN_EVENT(StartStall);
            prev_.wait();
        }

        if (block_state_.can_merge(state)) {
            if (result.has_error()) {
                return std::move(result.error());
            }
            auto const receipt = execute_final(state, result.value());
            block_state_.merge(state);
            return receipt;
        }
    }
    ++block_metrics_.num_retries;
    {
        TRACE_TXN_EVENT(StartRetry);

        State state{block_state_, Incarnation{header_.number, i_ + 1}};

        call_tracer_.reset();
        trace::reset(state_tracer_);

        auto result = execute_impl2(state);

        MONAD_ASSERT_THROW(
            block_state_.can_merge(state), "block state cannot be merged");
        if (result.has_error()) {
            return std::move(result.error());
        }
        auto const receipt = execute_final(state, result.value());
        block_state_.merge(state);
        return receipt;
    }
}

EXPLICIT_TRAITS_CLASS(ExecuteTransaction);

MONAD_NAMESPACE_END
