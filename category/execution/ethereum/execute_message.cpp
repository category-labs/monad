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
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/create_contract_address.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/execution/ethereum/native_transfer_log.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>

#include <algorithm>
#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace
{

    // The gas one access check of a private domain may use: the spoke's lookup
    // of the policy, its call to the policy and the policy's storage reads.
    constexpr int64_t DOMAIN_ACCESS_CHECK_GAS = 50'000;

    // Calldata of the spoke's canCall(address caller, address context, bytes
    // data) for the frame `msg`.
    byte_string encode_can_call(vm::Message const &msg)
    {
        constexpr uint32_t selector =
            abi_encode_selector("canCall(address,address,bytes)");
        byte_string calldata{
            static_cast<uint8_t>(selector >> 24),
            static_cast<uint8_t>(selector >> 16),
            static_cast<uint8_t>(selector >> 8),
            static_cast<uint8_t>(selector)};
        AbiEncoder encoder;
        encoder.add_address(msg.sender);
        encoder.add_address(msg.recipient);
        encoder.add_bytes({msg.input_data, msg.input_size});
        calldata += encoder.encode_final();
        return calldata;
    }

    // Whether `result` returns the ABI encoding of true and nothing else.
    bool returns_true(vm::Result const &result)
    {
        auto const expected = abi_encode_bool(true);
        return result.status_code == CallStatus::Success &&
               result.output_size == sizeof(expected.bytes) &&
               std::equal(
                   result.output_data,
                   result.output_data + result.output_size,
                   expected.bytes);
    }

    // Asks `spoke` whether the frame `msg` of a private domain may run, in a
    // static call that `gas`, the frame's gas, pays for. The spoke may call
    // the policy of the frame's contract, which may call nothing. Anything but
    // true from within DOMAIN_ACCESS_CHECK_GAS denies the frame.
    template <Traits traits>
    bool check_domain_access(
        StateHost<traits> &host, State &state, vm::Message const &msg,
        Address const &spoke, int64_t &gas)
    {
        if (gas < DOMAIN_ACCESS_CHECK_GAS) {
            return false;
        }
        auto const calldata = encode_can_call(msg);
        vm::Message const check{
            .kind = vm::CallKind::Call,
            .flags = std::to_underlying(vm::CallFlags::Static),
            .depth = msg.depth + 1,
            .gas = DOMAIN_ACCESS_CHECK_GAS,
            .recipient = spoke,
            .sender = msg.sender,
            .input_data = calldata.data(),
            .input_size = calldata.size(),
            .value = {},
            .create2_salt = {},
            .code_address = spoke,
            .memory_handle = msg.memory_handle,
            .memory = msg.memory,
            .memory_capacity = msg.memory_capacity,
        };
        host.domain_access_check_depth_ = check.depth;
        auto const result = execute_call_message<traits>(&host, state, check);
        host.domain_access_check_depth_ = -1;
        MONAD_ASSERT(
            result.gas_left >= 0 && result.gas_left <= DOMAIN_ACCESS_CHECK_GAS);
        gas -= DOMAIN_ACCESS_CHECK_GAS - result.gas_left;
        return !host.domain_access_denied_ && returns_true(result);
    }

    bool sender_has_balance(State &state, vm::Message const &msg) noexcept
    {
        uint256_t const value = load_be<uint256_t>(msg.value);
        // for optimistic execution, we do NOT require the original balance to
        // match exactly, just add a lower bound constraint to suffice for this
        // debit
        return state.record_balance_constraint_for_debit(msg.sender, value);
    }

    template <Traits traits>
    void transfer_balances(
        State &state, StateHost<traits> &host, vm::Message const &msg,
        Address const &to)
    {
        uint256_t const value = load_be<uint256_t>(msg.value);
        state.subtract_from_balance(msg.sender, value);
        state.add_to_balance(to, value);
        emit_native_transfer_logs<traits>(
            state,
            host.get_call_tracer(),
            msg.sender,
            to,
            value,
            host.log_native_transfers_);
    }

} // anonymous namespace

template <Traits traits>
vm::Result deploy_contract_code(
    State &state, Address const &address, vm::Result result) noexcept
{
    static_assert(traits::evm_rev() >= EvmRevision::SpuriousDragon);

    MONAD_ASSERT(result.status_code == CallStatus::Success);

    if constexpr (traits::eip_3541_active()) {
        if (result.output_size > 0 && result.output_data[0] == 0xef) {
            return vm::Result{CallStatus::ContractValidationFailure};
        }
    }
    // EIP-170
    if (result.output_size > traits::max_code_size()) {
        return vm::Result{CallStatus::OutOfGas};
    }

    auto const deploy_cost = static_cast<int64_t>(result.output_size) * 200;

    if (result.gas_left < deploy_cost) {
        // EIP-2: If contract creation does not have enough gas to
        // pay for the final gas fee for adding the contract code to
        // the state, the contract creation fails (ie. goes
        // out-of-gas) rather than leaving an empty contract.
        result.status_code = CallStatus::OutOfGas;
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
std::optional<vm::Result>
pre_call(StateHost<traits> &host, vm::Message const &msg, State &state)
{
    state.push();

    bool const static_call =
        msg.flags & std::to_underlying(vm::CallFlags::Static);

    if (msg.kind != vm::CallKind::DelegateCall) {
        if (MONAD_UNLIKELY(!sender_has_balance(state, msg))) {
            // The pushed frame exits before bytecode, account access, or
            // storage access, so there is no access-list metadata to capture.
            state.pop_reject();
            return vm::Result{CallStatus::InsufficientBalance, msg.gas};
        }
        else if (!static_call) {
            transfer_balances<traits>(state, host, msg, msg.recipient);
        }
    }

    if constexpr (!traits::eip_7702_active()) {
        MONAD_ASSERT(
            msg.kind != vm::CallKind::Call ||
            msg.recipient == msg.code_address);
    }

    if (msg.kind == vm::CallKind::Call && static_call) {
        // eip-161
        state.touch(msg.recipient);
    }

    return std::nullopt;
}

template <Traits traits>
void reject_frame(StateHost<traits> &host, State &state)
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
void post_call(StateHost<traits> &host, State &state, vm::Result const &result)
{
    MONAD_ASSERT(
        result.status_code == CallStatus::Success || result.gas_refund == 0);
    MONAD_ASSERT(
        result.status_code == CallStatus::Success ||
        result.status_code == CallStatus::Revert ||
        result.status_code == CallStatus::ReserveBalanceViolation ||
        result.gas_left == 0);

    if (result.status_code == CallStatus::Success) {
        state.pop_accept();
    }
    else {
        reject_frame(host, state);
    }
}

template <Traits traits>
vm::Result execute_create_message(
    StateHost<traits> *const host, State &state, vm::Message const &msg)
{
    static_assert(traits::evm_rev() >= EvmRevision::SpuriousDragon);

    MONAD_ASSERT(
        msg.kind == vm::CallKind::Create || msg.kind == vm::CallKind::Create2);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    if (MONAD_UNLIKELY(!sender_has_balance(state, msg))) {
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
                uint64_t const nonce = state.get_nonce(msg.sender);
                MONAD_ASSERT(nonce != UINT64_MAX);
                state.set_nonce(msg.sender, nonce + 1);
            }
        }
        vm::Result result{CallStatus::InsufficientBalance, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }

    auto const nonce = state.get_nonce(msg.sender);
    if (nonce == UINT64_MAX) {
        // this overflow can only happen for msg.depth != 0
        vm::Result result{CallStatus::ArgumentOutOfRange, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }
    state.set_nonce(msg.sender, nonce + 1);

    Address const contract_address = [&] {
        if (msg.kind == vm::CallKind::Create) {
            return create_contract_address(msg.sender, nonce); // YP Eqn. 85
        }
        else { // msg.kind == vm::CallKind::Create2
            auto const code_hash = keccak256({msg.input_data, msg.input_size});
            return create2_contract_address(
                msg.sender, msg.create2_salt, code_hash);
        }
    }();

    state.access_account(contract_address);

    // Prevent overwriting contracts - EIP-684
    if (state.account_has_code_or_nonce(contract_address)) {
        vm::Result result{CallStatus::InvalidInstruction};
        call_tracer.on_exit(result);
        return result;
    }

    state.push();

    state.create_contract(contract_address);

    // EIP-161
    state.set_nonce(contract_address, 1);
    transfer_balances<traits>(state, *host, msg, contract_address);

    vm::Message const m_call{
        .kind = vm::CallKind::Call,
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

    if (result.status_code == CallStatus::Success) {
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
            result.status_code = CallStatus::ReserveBalanceViolation;
        }
        if (MONAD_UNLIKELY(
                host->domain_access_denied_ &&
                result.status_code == CallStatus::Success)) {
            // A denied frame reverts the transaction, whatever its callers
            // made of it.
            result = vm::Result{CallStatus::Revert, result.gas_left};
        }
    }

    if (result.status_code == CallStatus::Success) {
        state.pop_accept();
    }
    else {
        result.gas_refund = 0;
        if (result.status_code != CallStatus::Revert) {
            result.gas_left = 0;
        }
        reject_frame(*host, state);
    }

    call_tracer.on_exit(result);

    return result;
}

EXPLICIT_TRAITS(execute_create_message);

template <Traits traits>
vm::Result execute_call_message(
    StateHost<traits> *const host, State &state, vm::Message const &msg)
{
    MONAD_ASSERT(
        msg.kind == vm::CallKind::DelegateCall ||
        msg.kind == vm::CallKind::CallCode || msg.kind == vm::CallKind::Call);

    auto &call_tracer = host->get_call_tracer();
    call_tracer.on_enter(msg);

    if (MONAD_UNLIKELY(
            host->domain_access_check_depth_ >= 0 &&
            msg.depth > host->domain_access_check_depth_ + 1)) {
        // The policy of an access check has called something.
        host->domain_access_denied_ = true;
        vm::Result result{CallStatus::Revert, msg.gas};
        call_tracer.on_exit(result);
        return result;
    }

    if (auto result = pre_call<traits>(*host, msg, state); result.has_value()) {
        call_tracer.on_exit(result.value());
        return std::move(result.value());
    }

    bool const private_domain = is_private_domain(host->chain_ctx_);

    // The frame that runs: on a private domain it pays for its access check.
    std::optional<vm::Message> checked;
    if (MONAD_UNLIKELY(private_domain)) {
        auto const *const spoke = domain_access_spoke(host->chain_ctx_);
        if (spoke != nullptr && host->domain_access_check_depth_ < 0) {
            checked.emplace(msg);
            if (!check_domain_access<traits>(
                    *host, state, msg, *spoke, checked->gas)) {
                host->domain_access_denied_ = true;
                vm::Result result{CallStatus::Revert, checked->gas};
                reject_frame(*host, state);
                call_tracer.on_exit(result);
                return result;
            }
        }
    }
    vm::Message const &frame = checked.has_value() ? *checked : msg;

    vm::Result result;
    // A private domain has no Monad precompiles: they read and write the
    // L1's staking and reserve balance state.
    if (auto maybe_result =
            private_domain
                ? check_call_eth_precompile<traits>(frame)
                : check_call_precompile<traits>(
                      state, call_tracer, frame, host->log_native_transfers_);
        maybe_result.has_value()) {
        result = std::move(maybe_result.value());
    }
    else {
        auto const hash = state.get_code_hash(frame.code_address);
        auto const code = state.read_code(hash);
        trace::on_read_code(host->state_tracer_, hash, code->intercode());
        result = state.vm().execute<traits>(*host, &frame, hash, code);
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
            result.status_code = CallStatus::ReserveBalanceViolation;
            result.gas_refund = 0;
        }
        if (MONAD_UNLIKELY(
                host->domain_access_denied_ &&
                result.status_code == CallStatus::Success)) {
            // A denied frame reverts the transaction, whatever its callers
            // made of it.
            result = vm::Result{CallStatus::Revert, result.gas_left};
        }
    }

    post_call(*host, state, result);
    call_tracer.on_exit(result);
    return result;
}

EXPLICIT_TRAITS(execute_call_message);
MONAD_NAMESPACE_END
