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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <cstring>
#include <limits>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace
{

    constexpr int64_t DOMAIN_ACCESS_GAS_STIPEND = 30'000;
    constexpr uint32_t CAN_CALL_SELECTOR =
        abi_encode_selector("canCall(address,address,bytes)");

    byte_string domain_access_calldata(evmc_message const &msg)
    {
        byte_string calldata{
            static_cast<uint8_t>(CAN_CALL_SELECTOR >> 24),
            static_cast<uint8_t>(CAN_CALL_SELECTOR >> 16),
            static_cast<uint8_t>(CAN_CALL_SELECTOR >> 8),
            static_cast<uint8_t>(CAN_CALL_SELECTOR)};
        AbiEncoder encoder;
        encoder.add_address(Address{msg.sender});
        encoder.add_address(Address{msg.recipient});
        encoder.add_bytes({msg.input_data, msg.input_size});
        calldata += encoder.encode_final();
        return calldata;
    }

    bool is_canonical_true(evmc::Result const &result) noexcept
    {
        if (result.status_code != EVMC_SUCCESS || result.output_size != 32) {
            return false;
        }
        auto const expected = abi_encode_bool(true);
        return std::memcmp(result.output_data, expected.bytes, 32) == 0;
    }

    void finalize_domain_access(
        evmc_message const &msg, bool const domain_access_denied,
        evmc::Result &result)
    {
        if (msg.depth == 0 && domain_access_denied &&
            result.status_code == EVMC_SUCCESS) {
            auto const gas_left = result.gas_left;
            result = evmc::Result{EVMC_REVERT, gas_left};
        }
    }

    bool sender_has_balance(State &state, evmc_message const &msg) noexcept
    {
        uint256_t const value = load_be<uint256_t>(msg.value);
        // for optimistic execution, we do NOT require the original balance to
        // match exactly, just add a lower bound constraint to suffice for this
        // debit
        return state.record_balance_constraint_for_debit(msg.sender, value);
    }

    template <Traits traits, bool gasless>
    void transfer_balances(
        State &state, EvmcHost<traits, gasless> &host, evmc_message const &msg,
        Address const &to)
    {
        uint256_t const value = load_be<uint256_t>(msg.value);
        state.subtract_from_balance(msg.sender, value);
        state.add_to_balance(to, value);
        host.emit_native_transfer_event(msg.sender, to, value);
    }

} // anonymous domain

template <Traits traits>
evmc::Result deploy_contract_code(
    State &state, Address const &address, evmc::Result result) noexcept
{
    static_assert(traits::evm_rev() >= MONAD_ETH_SPURIOUS_DRAGON);

    MONAD_ASSERT(result.status_code == EVMC_SUCCESS);

    // EIP-3541
    if constexpr (traits::evm_rev() >= MONAD_ETH_LONDON) {
        if (result.output_size > 0 && result.output_data[0] == 0xef) {
            return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
        }
    }
    // EIP-170
    if (result.output_size > traits::max_code_size()) {
        return evmc::Result{EVMC_OUT_OF_GAS};
    }

    auto const deploy_cost = static_cast<int64_t>(result.output_size) * 200;

    if (result.gas_left < deploy_cost) {
        // EIP-2: If contract creation does not have enough gas to
        // pay for the final gas fee for adding the contract code to
        // the state, the contract creation fails (ie. goes
        // out-of-gas) rather than leaving an empty contract.
        result.status_code = EVMC_OUT_OF_GAS;
    }
    else {
        result.create_address = address;
        result.gas_left -= deploy_cost;
        state.set_code(address, {result.output_data, result.output_size});
    }
    return result;
}

EXPLICIT_TRAITS(deploy_contract_code);

template <Traits traits, bool gasless>
void reject_frame(EvmcHost<traits, gasless> &host, State &state)
{
    // Successful frames remain in State and are captured when the state tracer
    // is encoded. Failed frames are about to be rolled back, so the state
    // tracer lifecycle hook runs before pop_reject().
    trace::on_frame_reject(host.state_tracer_, state);

    bool const ripemd_touched = state.is_touched(ripemd_address);
    state.pop_reject();
    if (MONAD_UNLIKELY(ripemd_touched)) {
        // YP K.1. Deletion of an Account Despite Out-of-gas.
        state.touch(ripemd_address);
    }
}

template <Traits traits, bool gasless>
std::optional<evmc::Result>
pre_call(EvmcHost<traits, gasless> &host, evmc_message &msg, State &state)
{
    state.push();

    if (host.domain_access_check_depth_ >= 0 &&
        msg.depth > host.domain_access_check_depth_ + 1) {
        // canCall and its direct callees may execute, but those callees must be
        // leaves. Make a deeper attempt transaction-sticky so it cannot be
        // hidden by catching this revert.
        host.domain_access_denied_ = true;
        state.pop_reject();
        return evmc::Result{EVMC_REVERT, msg.gas};
    }

    if (host.domain_spoke_.has_value() &&
        host.domain_access_check_depth_ == -1) {
        if (msg.gas < DOMAIN_ACCESS_GAS_STIPEND) {
            host.domain_access_denied_ = true;
            evmc::Result result{EVMC_REVERT, msg.gas};
            state.pop_reject();
            return result;
        }

        auto calldata = domain_access_calldata(msg);
        constexpr int64_t stipend = DOMAIN_ACCESS_GAS_STIPEND;
        evmc_message const access_msg{
            .kind = EVMC_CALL,
            .flags = EVMC_STATIC,
            .depth = msg.depth + 1,
            .gas = stipend,
            .recipient = *host.domain_spoke_,
            .sender = msg.sender,
            .input_data = calldata.data(),
            .input_size = calldata.size(),
            .value = {},
            .create2_salt = {},
            .code_address = *host.domain_spoke_,
            .memory_handle = msg.memory_handle,
            .memory = msg.memory,
            .memory_capacity = msg.memory_capacity,
        };

        MONAD_ASSERT(host.domain_access_check_depth_ == -1);
        MONAD_ASSERT(
            access_msg.depth >= 0 &&
            access_msg.depth <= std::numeric_limits<int16_t>::max());
        host.domain_access_check_depth_ =
            static_cast<int16_t>(access_msg.depth);
        auto access_result =
            execute_call_message<traits, gasless>(&host, state, access_msg);
        host.domain_access_check_depth_ = -1;

        bool const valid_gas =
            access_result.gas_left >= 0 && access_result.gas_left <= stipend;
        int64_t const gas_left = valid_gas ? access_result.gas_left : 0;
        msg.gas -= stipend - gas_left;

        if (host.domain_access_denied_ || !valid_gas ||
            !is_canonical_true(access_result)) {
            host.domain_access_denied_ = true;
            evmc::Result result{EVMC_REVERT, msg.gas};
            state.pop_reject();
            return result;
        }
    }

    bool const static_call = msg.flags & EVMC_STATIC;

    if (msg.kind != EVMC_DELEGATECALL) {
        if (MONAD_UNLIKELY(!sender_has_balance(state, msg))) {
            evmc::Result result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
            state.pop_reject();
            return result;
        }
        else if (!static_call) {
            transfer_balances<traits>(state, host, msg, msg.recipient);
        }
    }

    if constexpr (traits::evm_rev() < MONAD_ETH_PRAGUE) {
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

template <Traits traits, bool gasless>
void post_call(
    EvmcHost<traits, gasless> &host, State &state, evmc::Result const &result)
{
    MONAD_ASSERT(result.status_code == EVMC_SUCCESS || result.gas_refund == 0);
    MONAD_ASSERT(
        result.status_code == EVMC_SUCCESS ||
        result.status_code == EVMC_REVERT ||
        result.status_code == EVMC_MONAD_RESERVE_BALANCE_VIOLATION ||
        result.gas_left == 0);

    if (result.status_code == EVMC_SUCCESS) {
        state.pop_accept();
    }
    else {
        reject_frame(host, state);
    }
}

template <Traits traits, bool gasless>
evmc::Result execute_create_message(
    EvmcHost<traits, gasless> *const host, State &state,
    evmc_message const &msg)
{
    static_assert(traits::evm_rev() >= MONAD_ETH_SPURIOUS_DRAGON);

    MONAD_ASSERT(msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    if (MONAD_UNLIKELY(!sender_has_balance(state, msg))) {
        if constexpr (is_monad_trait_v<traits>) {
            /**
             * for Ethereum, at depth = 0, the sender always has sufficient
             * balance here as the transaction would be invalid otherwise
             *
             * for Monad, at depth = 0, this is not necessarily the case because
             * Monad has delayed execution with a reserve balance concept -
             * therefore we must be sure to increment the sender nonce if the
             * sender does not have sufficient balance
             */
            if constexpr (traits::monad_rev() >= MONAD_FIVE) {
                if (!msg.depth) {
                    uint64_t const nonce = state.get_nonce(msg.sender);
                    MONAD_ASSERT(nonce != UINT64_MAX);
                    state.set_nonce(msg.sender, nonce + 1);
                }
            }
        }
        evmc::Result result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }

    auto const nonce = state.get_nonce(msg.sender);
    if (nonce == UINT64_MAX) {
        // this overflow can only happen for msg.depth != 0
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
    state.set_nonce(contract_address, 1);
    transfer_balances<traits>(state, *host, msg, contract_address);

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
        .memory_handle = msg.memory_handle,
        .memory = msg.memory,
        .memory_capacity = msg.memory_capacity,
    };

    auto result = state.vm().execute_bytecode<traits>(
        *host, &m_call, {msg.input_data, msg.input_size});

    if (result.status_code == EVMC_SUCCESS) {
        result = deploy_contract_code<traits>(
            state, contract_address, std::move(result));
    }

    if constexpr (!gasless) {
        if (msg.depth == 0) {
            if (revert_transaction<traits>(
                    msg.sender,
                    host->tx_,
                    host->base_fee_per_gas_.value_or(0),
                    host->i_,
                    state,
                    host->state_tracer_,
                    host->chain_ctx_)) {
                result.status_code = EVMC_MONAD_RESERVE_BALANCE_VIOLATION;
            }
        }
    }

    if constexpr (gasless) {
        finalize_domain_access(msg, host->domain_access_denied_, result);
    }

    if (result.status_code == EVMC_SUCCESS) {
        state.pop_accept();
    }
    else {
        result.gas_refund = 0;
        if (result.status_code != EVMC_REVERT) {
            result.gas_left = 0;
        }
        reject_frame(*host, state);
    }

    call_tracer.on_exit(result);

    return result;
}

EXPLICIT_TRAITS(execute_create_message);
EXPLICIT_MONAD_TRAITS_TRUE(execute_create_message);

template <Traits traits, bool gasless>
evmc::Result execute_call_message(
    EvmcHost<traits, gasless> *const host, State &state,
    evmc_message const &msg)
{
    MONAD_ASSERT(
        msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE ||
        msg.kind == EVMC_CALL);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    evmc_message adjusted_msg = msg;
    if (auto result = pre_call<traits>(*host, adjusted_msg, state);
        result.has_value()) {
        call_tracer.on_exit(result.value());
        return std::move(result.value());
    }

    evmc::Result result;
    auto maybe_result = check_call_precompile<traits, gasless>(
        state, call_tracer, adjusted_msg);
    if (maybe_result.has_value()) {
        result = std::move(maybe_result.value());
    }
    else {
        auto const hash = state.get_code_hash(adjusted_msg.code_address);
        auto const code = state.read_code(hash);
        trace::on_read_code(host->state_tracer_, hash, code->intercode());
        result = state.vm().execute<traits>(*host, &adjusted_msg, hash, code);
    }

    if constexpr (!gasless) {
        if (msg.depth == 0) {
            if (revert_transaction<traits>(
                    msg.sender,
                    host->tx_,
                    host->base_fee_per_gas_.value_or(0),
                    host->i_,
                    state,
                    host->state_tracer_,
                    host->chain_ctx_)) {
                result.status_code = EVMC_MONAD_RESERVE_BALANCE_VIOLATION;
                result.gas_refund = 0;
            }
        }
    }

    if constexpr (gasless) {
        finalize_domain_access(msg, host->domain_access_denied_, result);
    }

    post_call(*host, state, result);
    call_tracer.on_exit(result);
    return result;
}

EXPLICIT_TRAITS(execute_call_message);
EXPLICIT_MONAD_TRAITS_TRUE(execute_call_message);
MONAD_NAMESPACE_END
