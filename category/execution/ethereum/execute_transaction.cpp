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
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/vm/evm/chain.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/switch_evm_chain.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <intx/intx.hpp>

#include <algorithm>
#include <functional>
#include <memory>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// YP Sec 6.2 "irrevocable_change"
template <Traits traits>
constexpr void irrevocable_change(
    State &state, Transaction const &tx, Address const &sender,
    uint256_t const &base_fee_per_gas, uint64_t const excess_blob_gas)
{
    if (tx.to) { // EVM will increment if new contract
        auto const nonce = state.get_nonce(sender);
        state.set_nonce(sender, nonce + 1);
    }

    uint256_t blob_gas = 0;
    if constexpr (traits::evm_rev() >= EVMC_CANCUN) {
        blob_gas = (tx.type == TransactionType::eip4844)
                       ? calc_blob_fee(tx, excess_blob_gas)
                       : 0;
    }
    auto const upfront_cost =
        tx.gas_limit * gas_price<traits>(tx, base_fee_per_gas);
    state.subtract_from_balance(sender, upfront_cost + blob_gas);
}

// YP Eqn 72 - template version for each revision
template <Traits traits>
constexpr uint64_t g_star(
    Transaction const &tx, uint64_t const gas_remaining, uint64_t const refund)
{
    // EIP-3529
    constexpr auto max_refund_quotient =
        traits::evm_rev() >= EVMC_LONDON ? 5 : 2;
    auto const refund_allowance =
        (tx.gas_limit - gas_remaining) / max_refund_quotient;
    return gas_remaining + std::min(refund_allowance, refund);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
ExecuteTransactionNoValidation<traits>::ExecuteTransactionNoValidation(
    Chain const &chain, Transaction const &tx, Address const &sender,
    std::vector<std::optional<Address>> const &authorities,
    BlockHeader const &header, uint64_t const i,
    RevertTransactionFn const &revert_transaction)
    : chain_{chain}
    , tx_{tx}
    , sender_{sender}
    , authorities_{authorities}
    , header_{header}
    , i_{i}
    , revert_transaction_{revert_transaction}
{
}

template <Traits traits>
ExecuteTransactionNoValidation<traits>::ExecuteTransactionNoValidation(
    Chain const &chain, Transaction const &tx, Address const &sender,
    BlockHeader const &header)
    : ExecuteTransactionNoValidation{chain, tx, sender, {}, header, 0}
{
}

// EIP-7702
template <Traits traits>
uint64_t ExecuteTransactionNoValidation<traits>::process_authorizations(
    State &state, EvmcHost<traits> &host)
{
    using namespace intx::literals;

    MONAD_ASSERT(authorities_.size() == tx_.authorization_list.size());

    uint64_t refund = 0u;

    for (auto i = 0u; i < tx_.authorization_list.size(); ++i) {
        auto const &auth_entry = tx_.authorization_list[i];
        MONAD_ASSERT(auth_entry.sc.chain_id.has_value());

        // 1. Verify the chain ID is 0 or the ID of the current chain.
        auto const &chain_id = *auth_entry.sc.chain_id;
        auto const host_chain_id =
            intx::be::load<uint256_t>(host.get_tx_context().chain_id);

        if (!(chain_id == 0 || chain_id == host_chain_id)) {
            continue;
        }

        // 2. Verify the nonce is less than 2**64 - 1.
        if (auth_entry.nonce == std::numeric_limits<uint64_t>::max()) {
            continue;
        }

        // 3. Let authority = ecrecover(msg, y_parity, r, s).
        auto const &authority = authorities_[i];
        if (!authority.has_value()) {
            continue;
        }

        static constexpr auto secp256k1_order =
            0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141_u256;
        if (auth_entry.sc.s > secp256k1_order / 2) {
            continue;
        }

        // 4. Add authority to accessed_addresses, as defined in EIP-2929.
        state.access_account(*authority);

        // 5. Verify the code of authority is empty or already delegated.
        auto const &icode = state.get_code(*authority)->intercode();
        auto const code = std::span{icode->code(), *icode->code_size()};
        if (!(code.empty() || vm::evm::is_delegated(code))) {
            continue;
        }

        // 6. Verify the nonce of authority is equal to nonce.
        auto const auth_nonce = state.get_nonce(*authority);
        if (auth_entry.nonce != auth_nonce) {
            continue;
        }

        if (!state.account_exists(*authority)) {
            // The authority processing step is happening before the transaction
            // runs, and so we need to create the account such that it cannot be
            // selfdestructed, even if the delegated code runs a `SELFDESTRUCT`
            // opcode. This is not documented explicitly in EIP-7702, but is a
            // consequence of the Cancun selfdestruct rules, and the fact that
            // authority processing (and therefore this account creation) are
            // not part of any transaction.
            state.create_account_no_rollback(*authority);
        }

        // 7. Add PER_EMPTY_ACCOUNT_COST - PER_AUTH_BASE_COST gas to the global
        // refund counter if authority is not empty.
        if (!is_empty(*state.recent_account(*authority))) {
            refund += (25'000u - 12'500u);
        }

        // 8. Set the code of authority to be 0xef0100 || address. This is a
        // delegation indicator.
        if (auth_entry.address) {
            auto const new_code =
                byte_string(vm::evm::delegation_indicator_prefix()) +
                byte_string(
                    auth_entry.address.bytes, auth_entry.address.bytes + 20);
            state.set_code(*authority, new_code);
        }
        else {
            // If address is 0x0000000000000000000000000000000000000000, do not
            // write the delegation indicator. Clear the account’s code
            state.set_code(*authority, {});
        }

        // 9. Increase the nonce of authority by one.
        state.set_nonce(*authority, auth_nonce + 1);
    }

    return refund;
}

template <Traits traits>
evmc_message ExecuteTransactionNoValidation<traits>::to_message() const
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
        .gas = static_cast<int64_t>(tx_.gas_limit - intrinsic_gas<traits>(tx_)),
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

template <Traits traits>
evmc::Result ExecuteTransactionNoValidation<traits>::operator()(
    State &state, EvmcHost<traits> &host)
{
    irrevocable_change<traits>(
        state,
        tx_,
        sender_,
        header_.base_fee_per_gas.value_or(0),
        header_.excess_blob_gas.value_or(0));

    // EIP-7702
    uint64_t auth_refund = 0u;
    if constexpr (traits::evm_rev() >= EVMC_PRAGUE) {
        auth_refund = process_authorizations(state, host);
    }

    // EIP-3651
    if constexpr (traits::evm_rev() >= EVMC_SHANGHAI) {
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

    auto msg = to_message();

    // EIP-7702
    if constexpr (traits::evm_rev() >= EVMC_PRAGUE) {
        if (tx_.to.has_value()) {
            if (auto const delegate = vm::evm::resolve_delegation(
                    &host.get_interface(), host.to_context(), *tx_.to)) {
                msg.code_address = *delegate;
                msg.flags |= EVMC_DELEGATED;
                state.access_account(*delegate);
            }
        }
    }

    auto result =
        (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2)
            ? ::monad::create<traits>(
                  &host,
                  state,
                  msg,
                  chain_.get_max_code_size(header_.number, header_.timestamp))
            : ::monad::call<traits>(&host, state, msg, [this, &state] {
                  return revert_transaction_(sender_, tx_, i_, state);
              });

    result.gas_refund += auth_refund;
    return result;
}

template class ExecuteTransactionNoValidation<EvmChain<EVMC_FRONTIER>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_HOMESTEAD>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_TANGERINE_WHISTLE>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_SPURIOUS_DRAGON>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_BYZANTIUM>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_CONSTANTINOPLE>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_PETERSBURG>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_ISTANBUL>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_BERLIN>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_LONDON>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_PARIS>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_SHANGHAI>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_CANCUN>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_PRAGUE>>;
template class ExecuteTransactionNoValidation<EvmChain<EVMC_OSAKA>>;

template <Traits traits>
ExecuteTransaction<traits>::ExecuteTransaction(
    Chain const &chain, uint64_t const i, Transaction const &tx,
    Address const &sender,
    std::vector<std::optional<Address>> const &authorities,
    BlockHeader const &header, BlockHashBuffer const &block_hash_buffer,
    BlockState &block_state, BlockMetrics &block_metrics,
    boost::fibers::promise<void> &prev, CallTracerBase &call_tracer,
    RevertTransactionFn const &revert_transaction)
    : ExecuteTransactionNoValidation<
          traits>{chain, tx, sender, authorities, header, i, revert_transaction}
    , block_hash_buffer_{block_hash_buffer}
    , block_state_{block_state}
    , block_metrics_{block_metrics}
    , prev_{prev}
    , call_tracer_{call_tracer}
{
}

template <Traits traits>
Result<evmc::Result> ExecuteTransaction<traits>::execute_impl2(State &state)
{
    auto const validate_lambda = [this, &state] {
        auto result = chain_.validate_transaction(
            header_.number,
            header_.timestamp,
            tx_,
            sender_,
            state,
            header_.base_fee_per_gas.value_or(0));
        if (!result) {
            // RELAXED MERGE
            // if `validate_transaction` fails using current values, require
            // exact match during merge as a precaution
            state.original_account_state(sender_).set_validate_exact_balance();
        }
        return result;
    };
    BOOST_OUTCOME_TRY(validate_lambda());

    auto const tx_context =
        get_tx_context<traits>(tx_, sender_, header_, chain_.get_chain_id());
    EvmcHost<traits> host{
        chain_,
        call_tracer_,
        tx_context,
        block_hash_buffer_,
        state,
        chain_.get_max_code_size(header_.number, header_.timestamp),
        chain_.get_max_initcode_size(header_.number, header_.timestamp),
        chain_.get_create_inside_delegated(),
        [this, &state] {
            return revert_transaction_(sender_, tx_, i_, state);
        }};

    return ExecuteTransactionNoValidation<traits>::operator()(state, host);
}

template <Traits traits>
Receipt ExecuteTransaction<traits>::execute_final(
    State &state, evmc::Result const &result)
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
        gas_price<traits>(tx_, header_.base_fee_per_gas.value_or(0));
    state.add_to_balance(sender_, gas_cost * gas_refund);

    auto gas_used = tx_.gas_limit - gas_refund;

    // EIP-7623
    if constexpr (traits::evm_rev() >= EVMC_PRAGUE) {
        auto const floor_gas = floor_data_gas(tx_);
        if (gas_used < floor_gas) {
            auto const delta = floor_gas - gas_used;
            state.subtract_from_balance(sender_, gas_cost * delta);

            gas_used = floor_gas;
        }
    }

    auto const reward = calculate_txn_award<traits>(
        tx_, header_.base_fee_per_gas.value_or(0), gas_used);
    state.add_to_balance(header_.beneficiary, reward);

    // finalize state, Eqn. 77-79
    state.destruct_suicides<traits>();
    if constexpr (traits::evm_rev() >= EVMC_SPURIOUS_DRAGON) {
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

template <Traits traits>
Result<Receipt> ExecuteTransaction<traits>::operator()()
{
    TRACE_TXN_EVENT(StartTxn);

    BOOST_OUTCOME_TRY(static_validate_transaction<traits>(
        tx_,
        header_.base_fee_per_gas,
        header_.excess_blob_gas,
        chain_.get_chain_id(),
        chain_.get_max_code_size(header_.number, header_.timestamp)));

    {
        TRACE_TXN_EVENT(StartExecution);

        State state{
            block_state_,
            Incarnation{header_.number, i_ + 1},
            /*relaxed_validation=*/true};
        state.set_original_nonce(sender_, tx_.nonce);

        call_tracer_.reset();

        auto result = execute_impl2(state);

        {
            TRACE_TXN_EVENT(StartStall);
            prev_.get_future().wait();
        }

        if (block_state_.can_merge(state)) {
            if (result.has_error()) {
                return std::move(result.error());
            }
            auto const receipt = execute_final(state, result.value());
            call_tracer_.on_finish(receipt.gas_used);
            block_state_.merge(state);
            return receipt;
        }
    }
    block_metrics_.inc_retries();
    {
        TRACE_TXN_EVENT(StartRetry);

        State state{block_state_, Incarnation{header_.number, i_ + 1}};

        call_tracer_.reset();

        auto result = execute_impl2(state);

        MONAD_ASSERT(block_state_.can_merge(state));
        if (result.has_error()) {
            return std::move(result.error());
        }
        auto const receipt = execute_final(state, result.value());
        call_tracer_.on_finish(receipt.gas_used);
        block_state_.merge(state);
        return receipt;
    }
}

template class ExecuteTransaction<EvmChain<EVMC_FRONTIER>>;
template class ExecuteTransaction<EvmChain<EVMC_HOMESTEAD>>;
template class ExecuteTransaction<EvmChain<EVMC_TANGERINE_WHISTLE>>;
template class ExecuteTransaction<EvmChain<EVMC_SPURIOUS_DRAGON>>;
template class ExecuteTransaction<EvmChain<EVMC_BYZANTIUM>>;
template class ExecuteTransaction<EvmChain<EVMC_CONSTANTINOPLE>>;
template class ExecuteTransaction<EvmChain<EVMC_PETERSBURG>>;
template class ExecuteTransaction<EvmChain<EVMC_ISTANBUL>>;
template class ExecuteTransaction<EvmChain<EVMC_BERLIN>>;
template class ExecuteTransaction<EvmChain<EVMC_LONDON>>;
template class ExecuteTransaction<EvmChain<EVMC_PARIS>>;
template class ExecuteTransaction<EvmChain<EVMC_SHANGHAI>>;
template class ExecuteTransaction<EvmChain<EVMC_CANCUN>>;
template class ExecuteTransaction<EvmChain<EVMC_PRAGUE>>;
template class ExecuteTransaction<EvmChain<EVMC_OSAKA>>;

uint64_t g_star(
    evmc_revision const rev, Transaction const &tx,
    uint64_t const gas_remaining, uint64_t const refund)
{
    SWITCH_EVM_CHAIN(g_star, tx, gas_remaining, refund);
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END
