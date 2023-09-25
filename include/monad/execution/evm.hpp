#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/create_contract_address.hpp>
#include <monad/execution/precompiles.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <tl/expected.hpp>

#include <limits>
#include <optional>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <
    class TState, concepts::fork_traits<TState> TTraits, class TInterpreter>
struct Evm
{
    using result_t = tl::expected<void, evmc_result>;
    using unexpected_t = tl::unexpected<evmc_result>;

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result create_contract_account(
        TEvmHost *host, TState &state, evmc_message const &m) noexcept
    {
        if (auto const result = check_sender_balance(state, m);
            !result.has_value()) {
            return evmc::Result{result.error()};
        }

        auto const nonce = state.get_nonce(m.sender);
        if (nonce == std::numeric_limits<decltype(nonce)>::max()) {
            // Match geth behavior - don't overflow nonce
            return evmc::Result{EVMC_ARGUMENT_OUT_OF_RANGE, m.gas};
        }
        state.set_nonce(m.sender, nonce + 1);

        auto const contract_address = [&] {
            if (m.kind == EVMC_CREATE) {
                return create_contract_address(m.sender, nonce); // YP Eqn. 85
            }
            else if (m.kind == EVMC_CREATE2) {
                auto const code_hash =
                    ethash::keccak256(m.input_data, m.input_size);
                return create2_contract_address(
                    m.sender, m.create2_salt, code_hash);
            }
            std::unreachable();
        }();

        state.access_account(contract_address);

        // Prevent overwriting contracts - EIP-684
        if (state.account_exists(contract_address)) {
            return evmc::Result{EVMC_INVALID_INSTRUCTION};
        }

        TState new_state{state};
        TEvmHost new_host{*host, new_state};

        new_state.create_account(contract_address);
        new_state.set_nonce(contract_address, TTraits::starting_nonce());
        transfer_balances(new_state, m, contract_address);

        evmc_message const m_call{
            .kind = EVMC_CALL,
            .depth = m.depth,
            .gas = m.gas,
            .recipient = contract_address,
            .sender = m.sender,
            .value = m.value,
            .code_address = contract_address,
        };

        auto result = TInterpreter::execute(
            &new_host, m_call, byte_string_view(m.input_data, m.input_size));

        if (result.status_code == EVMC_SUCCESS) {
            result = TTraits::deploy_contract_code(
                new_state, contract_address, std::move(result));
        }

        if (result.status_code == EVMC_SUCCESS) {
            state.merge(new_state);
        }

        return result;
    }

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result
    call_evm(TEvmHost *host, TState &state, evmc_message const &m) noexcept
    {
        TState new_state{state};
        TEvmHost new_host{*host, new_state};

        if (auto const result = transfer_call_balances(new_state, m);
            result.status_code != EVMC_SUCCESS) {
            return evmc::Result{result};
        }

        MONAD_DEBUG_ASSERT(
            m.kind != EVMC_CALL ||
            address_t{m.recipient} == address_t{m.code_address});
        if (m.kind == EVMC_CALL && m.flags & EVMC_STATIC) {
            // eip-161
            new_state.touch(m.recipient);
        }

        evmc::Result result;
        if (auto maybe_result = check_call_precompile<TTraits>(m);
            maybe_result.has_value()) {
            result = std::move(maybe_result.value());
        }
        else {
            auto const code = new_state.get_code(m.code_address);
            result = TInterpreter::execute(&new_host, m, code);
        }

        if (result.status_code == EVMC_SUCCESS) {
            state.merge(new_state);
        }

        return result;
    }

    [[nodiscard]] static result_t
    check_sender_balance(TState &s, evmc_message const &m) noexcept
    {
        auto const value = intx::be::load<uint256_t>(m.value);
        auto const balance = intx::be::load<uint256_t>(s.get_balance(m.sender));
        if (balance < value) {
            return unexpected_t(
                {.status_code = EVMC_INSUFFICIENT_BALANCE, .gas_left = m.gas});
        }
        return {};
    }

    static void transfer_balances(
        TState &s, evmc_message const &m, address_t const &to) noexcept
    {
        auto const value = intx::be::load<uint256_t>(m.value);
        s.subtract_from_balance(m.sender, value);
        s.add_to_balance(to, value);
    }

    [[nodiscard]] static evmc_result
    transfer_call_balances(TState &s, evmc_message const &m)
    {
        if (m.kind != EVMC_DELEGATECALL) {
            if (auto const result = check_sender_balance(s, m);
                !result.has_value()) {
                return result.error();
            }
            else if (m.flags != EVMC_STATIC) {
                transfer_balances(s, m, m.recipient);
            }
        }
        return {.status_code = EVMC_SUCCESS};
    }
};

MONAD_EXECUTION_NAMESPACE_END
