#pragma once

#include <monad/config.hpp>

#include <monad/execution/create_contract_address.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>
#include <monad/execution/precompiles.hpp>

#include <monad/state2/state.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <tl/expected.hpp>

#include <limits>
#include <optional>

MONAD_NAMESPACE_BEGIN

template <class Traits>
struct Evm
{
    using interpreter_t = EVMOneBaselineInterpreter<Traits>;

    using result_t = tl::expected<void, evmc_result>;
    using unexpected_t = tl::unexpected<evmc_result>;

    static evmc::Result deploy_contract_code(
        State &state, address_t const &address, evmc::Result result) noexcept
    {
        MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);

        // https://eips.ethereum.org/EIPS/eip-3541
        if constexpr (Traits::rev >= EVMC_LONDON) {
            if (result.output_size > 0 && result.output_data[0] == 0xef) {
                return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
            }
        }
        // EIP-170
        if constexpr (Traits::rev >= EVMC_SPURIOUS_DRAGON) {
            if (result.output_size > Traits::max_code_size) {
                return evmc::Result{EVMC_OUT_OF_GAS};
            }
        }

        auto const deploy_cost = static_cast<int64_t>(result.output_size) * 200;

        if (result.gas_left < deploy_cost) {
            if constexpr (Traits::rev == EVMC_FRONTIER) {
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

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result create_contract_account(
        TEvmHost *host, State &state, evmc_message const &msg) noexcept
    {
        if (auto const result = check_sender_balance(state, msg);
            !result.has_value()) {
            return evmc::Result{result.error()};
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
            std::unreachable();
        }();

        state.access_account(contract_address);

        // Prevent overwriting contracts - EIP-684
        if (state.get_nonce(contract_address) != 0 ||
            state.get_code_hash(contract_address) != NULL_HASH) {
            return evmc::Result{EVMC_INVALID_INSTRUCTION};
        }

        State new_state{state};
        TEvmHost new_host{*host, new_state};

        new_state.create_contract(contract_address);

        // https://eips.ethereum.org/EIPS/eip-161
        constexpr auto starting_nonce =
            Traits::rev >= EVMC_SPURIOUS_DRAGON ? 1 : 0;
        new_state.set_nonce(contract_address, starting_nonce);
        transfer_balances(new_state, msg, contract_address);

        evmc_message const m_call{
            .kind = EVMC_CALL,
            .depth = msg.depth,
            .gas = msg.gas,
            .recipient = contract_address,
            .sender = msg.sender,
            .value = msg.value,
            .code_address = contract_address,
        };

        auto result = interpreter_t::execute(
            &new_host,
            m_call,
            byte_string_view(msg.input_data, msg.input_size));

        if (result.status_code == EVMC_SUCCESS) {
            result = deploy_contract_code(
                new_state, contract_address, std::move(result));
        }

        if (result.status_code == EVMC_SUCCESS) {
            state.merge(new_state);
        }
        else {
            result.gas_refund = 0;
            if (result.status_code != EVMC_REVERT) {
                result.gas_left = 0;
            }
            if (MONAD_UNLIKELY(new_state.is_touched(ripemd_address))) {
                // YP K.1. Deletion of an Account Despite Out-of-gas.
                state.touch(ripemd_address);
            }
        }

        return result;
    }

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result
    call_evm(TEvmHost *host, State &state, evmc_message const &msg) noexcept
    {
        State new_state{state};
        TEvmHost new_host{*host, new_state};

        if (auto const result = transfer_call_balances(new_state, msg);
            result.status_code != EVMC_SUCCESS) {
            return evmc::Result{result};
        }

        MONAD_DEBUG_ASSERT(
            msg.kind != EVMC_CALL ||
            address_t{msg.recipient} == address_t{msg.code_address});
        if (msg.kind == EVMC_CALL && msg.flags & EVMC_STATIC) {
            // eip-161
            new_state.touch(msg.recipient);
        }

        evmc::Result result;
        if (auto maybe_result = check_call_precompile<Traits>(msg);
            maybe_result.has_value()) {
            result = std::move(maybe_result.value());
        }
        else {
            auto const code = new_state.get_code(msg.code_address);
            result = interpreter_t::execute(&new_host, msg, code);
        }

        MONAD_DEBUG_ASSERT(
            result.status_code == EVMC_SUCCESS || result.gas_refund == 0);
        MONAD_DEBUG_ASSERT(
            result.status_code == EVMC_SUCCESS ||
            result.status_code == EVMC_REVERT || result.gas_left == 0);

        if (result.status_code == EVMC_SUCCESS) {
            state.merge(new_state);
        }
        else if (MONAD_UNLIKELY(new_state.is_touched(ripemd_address))) {
            // YP K.1. Deletion of an Account Despite Out-of-gas.
            state.touch(ripemd_address);
        }

        return result;
    }

    [[nodiscard]] static result_t
    check_sender_balance(State &state, evmc_message const &msg) noexcept
    {
        auto const value = intx::be::load<uint256_t>(msg.value);
        auto const balance =
            intx::be::load<uint256_t>(state.get_balance(msg.sender));
        if (balance < value) {
            return unexpected_t(
                {.status_code = EVMC_INSUFFICIENT_BALANCE,
                 .gas_left = msg.gas});
        }
        return {};
    }

    static void transfer_balances(
        State &state, evmc_message const &msg, address_t const &to) noexcept
    {
        auto const value = intx::be::load<uint256_t>(msg.value);
        state.subtract_from_balance(msg.sender, value);
        state.add_to_balance(to, value);
    }

    [[nodiscard]] static evmc_result
    transfer_call_balances(State &state, evmc_message const &msg)
    {
        if (msg.kind != EVMC_DELEGATECALL) {
            if (auto const result = check_sender_balance(state, msg);
                !result.has_value()) {
                return result.error();
            }
            else if (msg.flags != EVMC_STATIC) {
                transfer_balances(state, msg, msg.recipient);
            }
        }
        return {.status_code = EVMC_SUCCESS};
    }
};

MONAD_NAMESPACE_END
