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
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/execution/ethereum/native_transfer_log.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <limits>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace
{
#if defined(MONAD_ZKVM_ZISK)
    // Zero has the same representation in either byte order.
    // memcpy reads each word without requiring alignment or type aliasing.
    [[gnu::always_inline]] inline bool
    is_zero_value(evmc_bytes32 const &v) noexcept
    {
        uint64_t w0;
        uint64_t w1;
        uint64_t w2;
        uint64_t w3;
        __builtin_memcpy(&w0, v.bytes, sizeof(w0));
        __builtin_memcpy(&w1, v.bytes + 8, sizeof(w1));
        __builtin_memcpy(&w2, v.bytes + 16, sizeof(w2));
        __builtin_memcpy(&w3, v.bytes + 24, sizeof(w3));
        return (w0 | w1 | w2 | w3) == 0;
    }

    constexpr uint256_t zero_value{};
#endif

    bool sender_has_balance(
        State &state, evmc_message const &msg,
        evmc_address const &sender) noexcept
    {
        uint256_t const value = load_be<uint256_t>(msg.value);
        // for optimistic execution, we do NOT require the original balance to
        // match exactly, just add a lower bound constraint to suffice for this
        // debit
        return state.record_balance_constraint_for_debit(sender, value);
    }

#if defined(MONAD_ZKVM_ZISK)
    bool sender_has_balance(
        State &state, evmc_address const &sender,
        uint256_t const &value) noexcept
    {
        return state.record_balance_constraint_for_debit(sender, value);
    }

    template <Traits traits>
    void transfer_balances(
        State &state, EvmcHost<traits> &host, evmc_address const &from,
        evmc_address const &to, uint256_t const &value)
    {
        if constexpr (!is_monad_trait_v<traits>) {
            // The caller has code or a nonce, so touching it cannot affect
            // EIP-161 cleanup. Keep the recipient touch; Ethereum has no
            // reserve tracking, and zero transfers emit no event.
            if (value == 0) {
                state.add_to_balance(to, value);
                return;
            }
        }
        state.subtract_from_balance(from, value);
        state.add_to_balance(to, value);
        emit_native_transfer_logs<traits>(
            state, host.get_call_tracer(), from, to, value,
            host.log_native_transfers_);
    }
#endif

    template <Traits traits>
    void transfer_balances(
        State &state, EvmcHost<traits> &host, evmc_message const &msg,
        evmc_address const &from, evmc_address const &to)
    {
        uint256_t const value = load_be<uint256_t>(msg.value);
        state.subtract_from_balance(from, value);
        state.add_to_balance(to, value);
        emit_native_transfer_logs<traits>(
            state,
            host.get_call_tracer(),
            from,
            to,
            value,
            host.log_native_transfers_);
    }

} // anonymous namespace

template <Traits traits>
evmc::Result deploy_contract_code(
    State &state, Address const &address, evmc::Result result) noexcept
{
    static_assert(traits::evm_rev() >= MONAD_ETH_SPURIOUS_DRAGON);

    MONAD_ASSERT(result.status_code == EVMC_SUCCESS);

    if constexpr (traits::eip_3541_active()) {
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

template <Traits traits>
std::optional<evmc::Result>
pre_call(EvmcHost<traits> &host, evmc_message const &msg, State &state)
{
    state.push();

    bool const static_call = msg.flags & EVMC_STATIC;

    if (msg.kind != EVMC_DELEGATECALL) {
        // Reuse the sender for the balance check and transfer.
        evmc_address const &sender = msg.sender;
#if defined(MONAD_ZKVM_ZISK) && defined(MONAD_ZKVM_NO_MERGE_CONSTRAINTS)
        // Skip decoding and the balance check for zero; keep transfer handling.
        if (MONAD_LIKELY(is_zero_value(msg.value))) {
            if (!static_call) {
                transfer_balances<traits>(
                    state, host, sender, msg.recipient, zero_value);
            }
        }
        else if (uint256_t const value = load_be<uint256_t>(msg.value);
                 MONAD_UNLIKELY(!sender_has_balance(state, sender, value))) {
            // No bytecode or access-list changes occurred in this frame.
            state.pop_reject();
            return evmc::Result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        }
        else if (!static_call) {
            transfer_balances<traits>(
                state, host, sender, msg.recipient, value);
        }
#else
    #if defined(MONAD_ZKVM_ZISK)
        // Decode once and reuse the value for the balance check and transfer.
        uint256_t const value = load_be<uint256_t>(msg.value);
        if (MONAD_UNLIKELY(!sender_has_balance(state, sender, value))) {
    #else
        if (MONAD_UNLIKELY(!sender_has_balance(state, msg, sender))) {
    #endif
            // The pushed frame exits before bytecode, account access, or
            // storage access, so there is no access-list metadata to capture.
            state.pop_reject();
            return evmc::Result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        }
        else if (!static_call) {
            evmc_address const &recipient = msg.recipient;
    #if defined(MONAD_ZKVM_ZISK)
            transfer_balances<traits>(state, host, sender, recipient, value);
    #else
            transfer_balances<traits>(state, host, msg, sender, recipient);
    #endif
        }
#endif
    }

    if constexpr (!traits::eip_7702_active()) {
        MONAD_ASSERT(
            msg.kind != EVMC_CALL ||
            address_equal(msg.recipient, msg.code_address));
    }

    if (msg.kind == EVMC_CALL && static_call) {
        // eip-161
        evmc_address const &recipient = msg.recipient;
        state.touch(recipient);
    }

    return std::nullopt;
}

template <Traits traits>
void reject_frame(EvmcHost<traits> &host, State &state)
{
    // Successful frames remain in State and are captured when the state tracer
    // is encoded. Failed frames are about to be rolled back, so the state
    // tracer lifecycle hook runs before pop_reject().
    trace::on_frame_reject(host.state_tracer_, state);

    // In contrast to YP K.1, Deletion of an Account Despite Out-of-gas,
    // we revert a touch of the ripemd address here. This is irrelevant in
    // all of the supported Ethereum forks, where the ripemd address is not
    // empty, and hence will not get destroyed later by EIP-161, even if it is
    // touched. For Monad, reverting touched is irrelevant, because the ripemd
    // account cannot even exist as an empty account according to EIP-161,
    // implemented by all Monad revisions. Although keeping a touch of the
    // ripemd address is harmless at the time of writing, it has been removed
    // because behavior depending on reverted state is generally non-
    // deterministic: reverted state depends on whether the bytecode was
    // executed as compiled native code or interpreted.
    state.pop_reject();
}

template <Traits traits>
void post_call(EvmcHost<traits> &host, State &state, evmc::Result const &result)
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

template <Traits traits>
evmc::Result execute_create_message(
    EvmcHost<traits> *const host, State &state, evmc_message const &msg)
{
    static_assert(traits::evm_rev() >= MONAD_ETH_SPURIOUS_DRAGON);

    MONAD_ASSERT(msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    evmc_address const &sender = msg.sender;
    if (MONAD_UNLIKELY(!sender_has_balance(state, msg, sender))) {
        /**
         * for Ethereum, at depth = 0, the sender always has sufficient
         * balance here as the transaction would be invalid otherwise
         *
         * for Monad, at depth = 0, this is not necessarily the case because
         * Monad has delayed execution with a reserve balance concept -
         * therefore we must be sure to increment the sender nonce if the
         * sender does not have sufficient balance
         */
        if constexpr (traits::bumps_nonce_on_unfunded_create()) {
            if (!msg.depth) {
                uint64_t const nonce = state.get_nonce(sender);
                MONAD_ASSERT(nonce != UINT64_MAX);
                state.set_nonce(sender, nonce + 1);
            }
        }
        evmc::Result result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }

    auto const nonce = state.get_nonce(sender);
    if (nonce == UINT64_MAX) {
        // this overflow can only happen for msg.depth != 0
        evmc::Result result{EVMC_ARGUMENT_OUT_OF_RANGE, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }
    state.set_nonce(sender, nonce + 1);

    Address const contract_address = [&] {
        if (msg.kind == EVMC_CREATE) {
            return create_contract_address(sender, nonce); // YP Eqn. 85
        }
        else { // msg.kind == EVMC_CREATE2
            auto const code_hash = keccak256({msg.input_data, msg.input_size});
            return create2_contract_address(
                sender, msg.create2_salt, code_hash);
        }
    }();

    state.access_account(contract_address);

    // Prevent overwriting contracts - EIP-684
    if (state.account_has_code_or_nonce(contract_address)) {
        evmc::Result result{EVMC_INVALID_INSTRUCTION};
        call_tracer.on_exit(result);
        return result;
    }

    state.push();

    state.create_contract(contract_address);

    // EIP-161
    state.set_nonce(contract_address, 1);
    transfer_balances<traits>(state, *host, msg, sender, contract_address);

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

template <Traits traits>
evmc::Result execute_call_message(
    EvmcHost<traits> *const host, State &state, evmc_message const &msg)
{
    MONAD_ASSERT(
        msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE ||
        msg.kind == EVMC_CALL);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    // Initialise directly to avoid clearing and move-assigning the result.
    // Return the same local on every path to enable NRVO.
    bool pre_called = false;
    evmc::Result result = [&] {
        if (auto pre_result = pre_call<traits>(*host, msg, state);
            pre_result.has_value()) {
            pre_called = true;
            return std::move(pre_result.value());
        }
        // Skip precompile lookup for ordinary addresses.
        if (may_be_precompile(msg.code_address)) {
            if (auto maybe_result =
                    check_call_precompile<traits>(
                        state, call_tracer, msg, host->log_native_transfers_);
                maybe_result.has_value()) {
                return std::move(maybe_result.value());
            }
        }
        evmc_address const &code_address = msg.code_address;
        auto const hash = state.get_code_hash(code_address);
#if defined(MONAD_ZKVM_VARCODE_CACHE)
        // The VM cache keeps the code alive. execute reads its intercode
        // before nested calls can replace State's cached pointer.
        auto const &code = state.read_code_ref(hash);
#else
        auto const code = state.read_code(hash);
#endif
        trace::on_read_code(host->state_tracer_, hash, code->intercode());
        return state.vm().execute<traits>(*host, &msg, hash, code);
    }();
    if (pre_called) {
        call_tracer.on_exit(result);
        return result;
    }

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

    post_call(*host, state, result);
    call_tracer.on_exit(result);
    return result;
}

EXPLICIT_TRAITS(execute_call_message);
MONAD_NAMESPACE_END
