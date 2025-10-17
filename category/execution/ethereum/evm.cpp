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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <ethash/hash_types.hpp>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>
#include <optional>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bool sender_has_balance(State &state, evmc_message const &msg) noexcept
{
    uint256_t const value = intx::be::load<uint256_t>(msg.value);
    // for optimistic execution, we do NOT require the original balance to match
    // exactly, just add a lower bound constraint to suffice for this debit
    return state.record_balance_constraint_for_debit(msg.sender, value);
}

void transfer_balances(State &state, evmc_message const &msg, Address const &to)
{
    uint256_t const value = intx::be::load<uint256_t>(msg.value);
    state.subtract_from_balance(msg.sender, value);
    state.add_to_balance(to, value);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
evmc::Result deploy_contract_code(
    State &state, Address const &address, evmc::Result result) noexcept
{
    MONAD_ASSERT(result.status_code == EVMC_SUCCESS);

    // EIP-3541
    if constexpr (traits::evm_rev() >= EVMC_LONDON) {
        if (result.output_size > 0 && result.output_data[0] == 0xef) {
            return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
        }
    }
    // EIP-170
    if constexpr (traits::evm_rev() >= EVMC_SPURIOUS_DRAGON) {
        if (result.output_size > traits::max_code_size()) {
            return evmc::Result{EVMC_OUT_OF_GAS};
        }
    }

    auto const deploy_cost =
        static_cast<int64_t>(result.output_size) * traits::code_deposit_cost();

    if (result.gas_left < deploy_cost) {
        if constexpr (traits::evm_rev() == EVMC_FRONTIER) {
            // From YP: "No code is deposited in the state if the gas
            // does not cover the additional per-byte contract deposit
            // fee, however, the value is still transferred and the
            // execution side- effects take place."
            result.create_address = address;
            state.set_code(address, {});
        }
        else {
            // EIP-2: If contract creation does not have enough gas to
            // pay for the final gas fee for adding the contract code to
            // the state, the contract creation fails (ie. goes
            // out-of-gas) rather than leaving an empty contract.
            result.status_code = EVMC_OUT_OF_GAS;
        }
    }
    else {
        result.create_address = address;
        result.gas_left -= deploy_cost;
        state.set_code(address, {result.output_data, result.output_size});
    }
    return result;
}

EXPLICIT_TRAITS(deploy_contract_code);

template <Traits traits>
std::optional<evmc::Result> pre_call(evmc_message const &msg, State &state)
{
    state.push();

    bool const static_call = msg.flags & EVMC_STATIC;

    if (msg.kind != EVMC_DELEGATECALL) {
        if (MONAD_UNLIKELY(!sender_has_balance(state, msg))) {
            state.pop_reject();
            return evmc::Result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        }
        else if (!static_call) {
            transfer_balances(state, msg, msg.recipient);
        }
    }

    if constexpr (traits::evm_rev() < EVMC_PRAGUE) {
        MONAD_ASSERT(
            msg.kind != EVMC_CALL ||
            Address{msg.recipient} == Address{msg.code_address});
    }

    if (msg.kind == EVMC_CALL && static_call) {
        // eip-161
        state.touch(msg.recipient);
    }

    return std::nullopt;
}

void post_call(State &state, evmc::Result const &result)
{
    MONAD_ASSERT(result.status_code == EVMC_SUCCESS || result.gas_refund == 0);
    MONAD_ASSERT(
        result.status_code == EVMC_SUCCESS ||
        result.status_code == EVMC_REVERT || result.gas_left == 0);

    if (result.status_code == EVMC_SUCCESS) {
        state.pop_accept();
    }
    else {
        bool const ripemd_touched = state.is_touched(ripemd_address);
        state.pop_reject();
        if (MONAD_UNLIKELY(ripemd_touched)) {
            // YP K.1. Deletion of an Account Despite Out-of-gas.
            state.touch(ripemd_address);
        }
    }
}

template <Traits traits>
evmc::Result create(
    EvmcHost<traits> *const host, State &state, evmc_message const &msg,
    std::function<bool()> const &revert_transaction)
{
    MONAD_ASSERT(msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    if (MONAD_UNLIKELY(!sender_has_balance(state, msg))) {
        evmc::Result result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }

    auto const nonce = state.get_nonce(msg.sender);
    if (nonce == std::numeric_limits<decltype(nonce)>::max()) {
        // overflow
        evmc::Result result{EVMC_ARGUMENT_OUT_OF_RANGE, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }
    state.set_nonce(msg.sender, nonce + 1);

    Address const contract_address = [&] {
        if (msg.kind == EVMC_CREATE) {
            return create_contract_address(msg.sender, nonce); // YP Eqn. 85
        }
        else { // msg.kind == EVMC_CREATE2
            auto const code_hash = keccak256({msg.input_data, msg.input_size});
            return create2_contract_address(
                msg.sender, msg.create2_salt, code_hash);
        }
    }();

    state.access_account(contract_address);

    // Prevent overwriting contracts - EIP-684
    if (state.get_nonce(contract_address) != 0 ||
        state.get_code_hash(contract_address) != NULL_HASH) {
        evmc::Result result{EVMC_INVALID_INSTRUCTION};
        call_tracer.on_exit(result);
        return result;
    }

    state.push();

    state.create_contract(contract_address);

    // EIP-161
    constexpr auto starting_nonce =
        traits::evm_rev() >= EVMC_SPURIOUS_DRAGON ? 1 : 0;
    state.set_nonce(contract_address, starting_nonce);
    transfer_balances(state, msg, contract_address);

    evmc_message const m_call{
        .kind = EVMC_CALL,
        .flags = 0,
        .depth = msg.depth,
        .gas = msg.gas,
        .recipient = contract_address,
        .sender = msg.sender,
        .input_data = nullptr,
        .input_size = 0,
        .value = msg.value,
        .create2_salt = {},
        .code_address = contract_address,
        .code = nullptr,
        .code_size = 0,
    };

    auto result = state.vm().execute_bytecode<traits>(
        *host, &m_call, {msg.input_data, msg.input_size});

    if (result.status_code == EVMC_SUCCESS) {
        result = deploy_contract_code<traits>(
            state, contract_address, std::move(result));
    }

    if (msg.depth == 0 && revert_transaction()) {
        result.status_code = EVMC_REVERT;
    }

    if (result.status_code == EVMC_SUCCESS) {
        state.pop_accept();
    }
    else {
        result.gas_refund = 0;
        if (result.status_code != EVMC_REVERT) {
            result.gas_left = 0;
        }
        bool const ripemd_touched = state.is_touched(ripemd_address);
        state.pop_reject();
        if (MONAD_UNLIKELY(ripemd_touched)) {
            // YP K.1. Deletion of an Account Despite Out-of-gas.
            state.touch(ripemd_address);
        }
    }

    call_tracer.on_exit(result);

    return result;
}

EXPLICIT_TRAITS(create);

template <Traits traits>
evmc::Result call(
    EvmcHost<traits> *const host, State &state, evmc_message const &msg,
    std::function<bool()> const &revert_transaction)
{
    MONAD_ASSERT(
        msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE ||
        msg.kind == EVMC_CALL);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    if (auto result = pre_call<traits>(msg, state); result.has_value()) {
        call_tracer.on_exit(result.value());
        return std::move(result.value());
    }

    evmc::Result result;
    if (auto maybe_result =
            check_call_precompile<traits>(state, call_tracer, msg);
        maybe_result.has_value()) {
        result = std::move(maybe_result.value());
    }
    else {
        auto const hash = state.get_code_hash(msg.code_address);
        auto const &code = state.read_code(hash);
        result = state.vm().execute<traits>(*host, &msg, hash, code);
    }

    if (msg.depth == 0 && revert_transaction()) {
        result.status_code = EVMC_REVERT;
        result.gas_refund = 0;
    }

    post_call(state, result);
    call_tracer.on_exit(result);
    return result;
}

EXPLICIT_TRAITS(call);

MONAD_NAMESPACE_END
