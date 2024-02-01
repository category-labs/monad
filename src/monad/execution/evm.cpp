#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/execution/baseline_execute.hpp>
#include <monad/execution/create_contract_address.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <cstdint>
#include <limits>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

std::optional<evmc::Result>
check_sender_balance(State &state, evmc_message const &msg) noexcept
{
    auto const value = intx::be::load<uint256_t>(msg.value);
    auto const balance =
        intx::be::load<uint256_t>(state.get_balance(msg.sender));
    if (balance < value) {
        return evmc::Result{EVMC_INSUFFICIENT_BALANCE, msg.gas};
    }
    return std::nullopt;
}

void transfer_balances(
    State &state, evmc_message const &msg, Address const &to) noexcept
{
    auto const value = intx::be::load<uint256_t>(msg.value);
    state.subtract_from_balance(msg.sender, value);
    state.add_to_balance(to, value);
}

evmc::Result transfer_call_balances(State &state, evmc_message const &msg)
{
    if (msg.kind != EVMC_DELEGATECALL) {
        if (auto result = check_sender_balance(state, msg);
            result.has_value()) {
            return std::move(result.value());
        }
        else if (msg.flags != EVMC_STATIC) {
            transfer_balances(state, msg, msg.recipient);
        }
    }
    return evmc::Result{EVMC_SUCCESS};
}

template <evmc_revision rev>
evmc::Result deploy_contract_code(
    State &state, Address const &address, evmc::Result result) noexcept
{
    MONAD_ASSERT(result.status_code == EVMC_SUCCESS);

    // EIP-3541
    if constexpr (rev >= EVMC_LONDON) {
        if (result.output_size > 0 && result.output_data[0] == 0xef) {
            return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
        }
    }
    // EIP-170
    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        if (result.output_size > 0x6000) {
            return evmc::Result{EVMC_OUT_OF_GAS};
        }
    }

    auto const deploy_cost = static_cast<int64_t>(result.output_size) * 200;

    if (result.gas_left < deploy_cost) {
        if constexpr (rev == EVMC_FRONTIER) {
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

EXPLICIT_EVMC_REVISION(deploy_contract_code);

template <evmc_revision rev>
evmc::Result create_contract_account(
    EvmcHost<rev> *const host, State &state, evmc_message const &msg) noexcept
{
    if (auto result = check_sender_balance(state, msg); result.has_value()) {
        return std::move(result.value());
    }

    auto const nonce = state.get_nonce(msg.sender);
    if (nonce == std::numeric_limits<decltype(nonce)>::max()) {
        // Match geth behavior - don't overflow nonce
        return evmc::Result{EVMC_ARGUMENT_OUT_OF_RANGE, msg.gas};
    }
    state.set_nonce(msg.sender, nonce + 1);

    auto const contract_address = [&] {
        if (msg.kind == EVMC_CREATE) {
            return create_contract_address(msg.sender, nonce); // YP Eqn. 85
        }
        else if (msg.kind == EVMC_CREATE2) {
            auto const code_hash =
                ethash::keccak256(msg.input_data, msg.input_size);
            return create2_contract_address(
                msg.sender, msg.create2_salt, code_hash);
        }
        MONAD_ASSERT(false);
    }();

    state.access_account(contract_address);

    // Prevent overwriting contracts - EIP-684
    if (state.get_nonce(contract_address) != 0 ||
        state.get_code_hash(contract_address) != NULL_HASH) {
        return evmc::Result{EVMC_INVALID_INSTRUCTION};
    }

    state.push();

    state.create_contract(contract_address);

    // EIP-161
    constexpr auto starting_nonce = rev >= EVMC_SPURIOUS_DRAGON ? 1 : 0;
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
    };

    auto result = baseline_execute(
        m_call,
        rev,
        host,
        byte_string_view(msg.input_data, msg.input_size));

    if (result.status_code == EVMC_SUCCESS) {
        result = deploy_contract_code<rev>(
            state, contract_address, std::move(result));
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

    return result;
}

EXPLICIT_EVMC_REVISION(create_contract_account);

template <evmc_revision rev>
evmc::Result call_evm(
    EvmcHost<rev> *const host, State &state, evmc_message const &msg) noexcept
{
    state.push();

    if (auto result = transfer_call_balances(state, msg);
        result.status_code != EVMC_SUCCESS) {
        state.pop_reject();
        return result;
    }

    MONAD_ASSERT(
        msg.kind != EVMC_CALL ||
        Address{msg.recipient} == Address{msg.code_address});
    if (msg.kind == EVMC_CALL && msg.flags & EVMC_STATIC) {
        // eip-161
        state.touch(msg.recipient);
    }

    evmc::Result result;
    if (auto maybe_result = check_call_precompile<rev>(msg);
        maybe_result.has_value()) {
        result = std::move(maybe_result.value());
    }
    else {
        auto const code = state.get_code(msg.code_address);
        result = baseline_execute(msg, rev, host, code);
    }

    MONAD_ASSERT(
        result.status_code == EVMC_SUCCESS || result.gas_refund == 0);
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

    return result;
}

EXPLICIT_EVMC_REVISION(call_evm);

MONAD_NAMESPACE_END
