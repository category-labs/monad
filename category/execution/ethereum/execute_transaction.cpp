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
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/switch_evmc_revision.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <intx/intx.hpp>

#include <algorithm>
#include <functional>
#include <memory>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// YP Sec 6.2 "irrevocable_change"
template <evmc_revision rev>
constexpr void irrevocable_change(
    State &state, Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas, uint64_t const excess_blob_gas)
{
    if (tx.to) { // EVM will increment if new contract
        auto const nonce = state.get_nonce(sender);
        state.set_nonce(sender, nonce + 1);
    }

    uint256_t blob_gas = 0;
    if constexpr (rev >= EVMC_CANCUN) {
        blob_gas = (tx.type == TransactionType::eip4844)
                       ? calc_blob_fee(tx, excess_blob_gas)
                       : 0;
    }
    auto const upfront_cost =
        tx.gas_limit * gas_price<rev>(tx, base_fee_per_gas);
    state.subtract_from_balance(sender, upfront_cost + blob_gas);
}

// YP Eqn 72 - template version for each revision
template <evmc_revision rev>
constexpr uint64_t g_star(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    // EIP-3529
    constexpr auto max_refund_quotient = rev >= EVMC_LONDON ? 5 : 2;
    auto const refund_allowance =
        (tx.gas_limit - gas_remaining) / max_refund_quotient;
    return gas_remaining + std::min(refund_allowance, refund);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
ExecuteTransactionNoValidation<rev>::ExecuteTransactionNoValidation(
    Chain const &chain, Transaction const &tx, Address const &sender,
    BlockHeader const &header)
    : chain_{chain}
    , tx_{tx}
    , sender_{sender}
    , header_{header}
{
}

template <evmc_revision rev>
evmc_message ExecuteTransactionNoValidation<rev>::to_message() const
{
    auto const to_address = [this] {
        if (tx_.to) {
            return std::pair{EVMC_CALL, *tx_.to};
        }
        return std::pair{EVMC_CREATE, Address{}};
    }();

    evmc_message msg{
        .kind = to_address.first,
        .flags = 0,
        .depth = 0,
        .gas = static_cast<int64_t>(tx_.gas_limit - intrinsic_gas<rev>(tx_)),
        .recipient = to_address.second,
        .sender = sender_,
        .input_data = tx_.data.data(),
        .input_size = tx_.data.size(),
        .value = {},
        .create2_salt = {},
        .code_address = to_address.second,
        .code = nullptr, // TODO
        .code_size = 0, // TODO
    };
    intx::be::store(msg.value.bytes, tx_.value);
    return msg;
}

template <evmc_revision rev>
evmc::Result ExecuteTransactionNoValidation<rev>::operator()(
    State &state, EvmcHost<rev> &host)
{
    irrevocable_change<rev>(
        state,
        tx_,
        sender_,
        header_.base_fee_per_gas.value_or(0),
        header_.excess_blob_gas.value_or(0));

    // EIP-3651
    if constexpr (rev >= EVMC_SHANGHAI) {
        host.access_account(header_.beneficiary);
    }

    state.access_account(sender_);
    for (auto const &ae : tx_.access_list) {
        state.access_account(ae.a);
        for (auto const &keys : ae.keys) {
            state.access_storage(ae.a, keys);
        }
    }
    if (MONAD_LIKELY(tx_.to)) {
        state.access_account(*tx_.to);
    }

    auto const msg = to_message();
    return (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2)
               ? ::monad::create<rev>(
                     &host,
                     state,
                     msg,
                     chain_.get_max_code_size(
                         header_.number, header_.timestamp))
               : ::monad::call<rev>(&host, state, msg);
}

template class ExecuteTransactionNoValidation<EVMC_FRONTIER>;
template class ExecuteTransactionNoValidation<EVMC_HOMESTEAD>;
template class ExecuteTransactionNoValidation<EVMC_TANGERINE_WHISTLE>;
template class ExecuteTransactionNoValidation<EVMC_SPURIOUS_DRAGON>;
template class ExecuteTransactionNoValidation<EVMC_BYZANTIUM>;
template class ExecuteTransactionNoValidation<EVMC_CONSTANTINOPLE>;
template class ExecuteTransactionNoValidation<EVMC_PETERSBURG>;
template class ExecuteTransactionNoValidation<EVMC_ISTANBUL>;
template class ExecuteTransactionNoValidation<EVMC_BERLIN>;
template class ExecuteTransactionNoValidation<EVMC_LONDON>;
template class ExecuteTransactionNoValidation<EVMC_PARIS>;
template class ExecuteTransactionNoValidation<EVMC_SHANGHAI>;
template class ExecuteTransactionNoValidation<EVMC_CANCUN>;
template class ExecuteTransactionNoValidation<EVMC_PRAGUE>;

template <evmc_revision rev>
ExecuteTransaction<rev>::ExecuteTransaction(
    Chain const &chain, uint64_t const i, Transaction const &tx,
    Address const &sender, BlockHeader const &header,
    BlockHashBuffer const &block_hash_buffer, BlockState &block_state,
    BlockMetrics &block_metrics, boost::fibers::promise<void> &prev)
    : ExecuteTransactionNoValidation<rev>{chain, tx, sender, header}
    , i_{i}
    , block_hash_buffer_{block_hash_buffer}
    , block_state_{block_state}
    , block_metrics_{block_metrics}
    , prev_{prev}
{
}

template <evmc_revision rev>
Result<evmc::Result> ExecuteTransaction<rev>::execute_impl2(
    State &state, CallTracerBase &call_tracer)
{
    auto const sender_account = state.recent_account(sender_);
    BOOST_OUTCOME_TRY(validate_transaction(tx_, sender_account));

    auto const tx_context =
        get_tx_context<rev>(tx_, sender_, header_, chain_.get_chain_id());
    EvmcHost<rev> host{
        call_tracer,
        tx_context,
        block_hash_buffer_,
        state,
        chain_.get_max_code_size(header_.number, header_.timestamp)};

    return ExecuteTransactionNoValidation<rev>::operator()(state, host);
}

template <evmc_revision rev>
Receipt
ExecuteTransaction<rev>::execute_final(State &state, evmc::Result const &result)
{
    MONAD_ASSERT(result.gas_left >= 0);
    MONAD_ASSERT(result.gas_refund >= 0);
    MONAD_ASSERT(tx_.gas_limit >= static_cast<uint64_t>(result.gas_left));

    // refund and priority, Eqn. 73-76
    auto const gas_refund = chain_.compute_gas_refund(
        header_.number,
        header_.timestamp,
        tx_,
        static_cast<uint64_t>(result.gas_left),
        static_cast<uint64_t>(result.gas_refund));
    auto const gas_cost =
        gas_price<rev>(tx_, header_.base_fee_per_gas.value_or(0));
    state.add_to_balance(sender_, gas_cost * gas_refund);

    auto gas_used = tx_.gas_limit - gas_refund;

    // EIP-7623
    if constexpr (rev >= EVMC_PRAGUE) {
        auto const floor_gas = floor_data_gas(tx_);
        if (gas_used < floor_gas) {
            auto const delta = floor_gas - gas_used;
            state.subtract_from_balance(sender_, gas_cost * delta);

            gas_used = floor_gas;
        }
    }

    auto const reward = calculate_txn_award<rev>(
        tx_, header_.base_fee_per_gas.value_or(0), gas_used);
    state.add_to_balance(header_.beneficiary, reward);

    // finalize state, Eqn. 77-79
    state.destruct_suicides<rev>();
    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    Receipt receipt{
        .status = result.status_code == EVMC_SUCCESS ? 1u : 0u,
        .gas_used = gas_used,
        .type = tx_.type};
    for (auto const &log : state.logs()) {
        receipt.add_log(std::move(log));
    }

    return receipt;
}

template <evmc_revision rev>
Result<ExecutionResult> ExecuteTransaction<rev>::operator()()
{
    TRACE_TXN_EVENT(StartTxn);

    BOOST_OUTCOME_TRY(static_validate_transaction<rev>(
        tx_,
        header_.base_fee_per_gas,
        header_.excess_blob_gas,
        chain_.get_chain_id(),
        chain_.get_max_code_size(header_.number, header_.timestamp)));

    {
        TRACE_TXN_EVENT(StartExecution);

        State state{block_state_, Incarnation{header_.number, i_ + 1}};
        state.set_original_nonce(sender_, tx_.nonce);

        std::unique_ptr<CallTracerBase> call_tracer =
            std::make_unique<CallTracer>(tx_);

        auto result = execute_impl2(state, *call_tracer);

        {
            TRACE_TXN_EVENT(StartStall);
            prev_.get_future().wait();
        }

        if (block_state_.can_merge(state)) {
            if (result.has_error()) {
                return std::move(result.error());
            }
            auto const receipt = execute_final(state, result.value());
            call_tracer->on_finish(receipt.gas_used);
            block_state_.merge(state);

            return ExecutionResult{
                .receipt = receipt,
                .call_frames = std::move(*call_tracer).get_frames()};
        }
    }
    block_metrics_.inc_retries();
    {
        TRACE_TXN_EVENT(StartRetry);

        State state{block_state_, Incarnation{header_.number, i_ + 1}};

        std::unique_ptr<CallTracerBase> call_tracer =
            std::make_unique<CallTracer>(tx_);

        auto result = execute_impl2(state, *call_tracer);

        MONAD_ASSERT(block_state_.can_merge(state));
        if (result.has_error()) {
            return std::move(result.error());
        }
        auto const receipt = execute_final(state, result.value());
        call_tracer->on_finish(receipt.gas_used);
        block_state_.merge(state);

        return ExecutionResult{
            .receipt = receipt,
            .call_frames = std::move(*call_tracer).get_frames()};
    }
}

template class ExecuteTransaction<EVMC_FRONTIER>;
template class ExecuteTransaction<EVMC_HOMESTEAD>;
template class ExecuteTransaction<EVMC_TANGERINE_WHISTLE>;
template class ExecuteTransaction<EVMC_SPURIOUS_DRAGON>;
template class ExecuteTransaction<EVMC_BYZANTIUM>;
template class ExecuteTransaction<EVMC_CONSTANTINOPLE>;
template class ExecuteTransaction<EVMC_PETERSBURG>;
template class ExecuteTransaction<EVMC_ISTANBUL>;
template class ExecuteTransaction<EVMC_BERLIN>;
template class ExecuteTransaction<EVMC_LONDON>;
template class ExecuteTransaction<EVMC_PARIS>;
template class ExecuteTransaction<EVMC_SHANGHAI>;
template class ExecuteTransaction<EVMC_CANCUN>;
template class ExecuteTransaction<EVMC_PRAGUE>;

uint64_t g_star(
    evmc_revision const rev, Transaction const &tx,
    uint64_t const gas_remaining, uint64_t const refund)
{
    SWITCH_EVMC_REVISION(g_star, tx, gas_remaining, refund);
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END
