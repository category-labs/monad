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
    using result_t = tl::expected<evmc_message, evmc_result>;
    using new_address_t = tl::expected<address_t, evmc_result>;
    using unexpected_t = tl::unexpected<evmc_result>;

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result create_contract_account(
        TEvmHost *host, TState &state, evmc_message const &m) noexcept
    {
        if (auto const result = increment_sender_nonce(state, m);
            result.has_value()) {
            return evmc::Result{result.value()};
        }

        TState new_state{state};
        TEvmHost new_host{*host, new_state};

        auto const contract_address = make_account_address(new_state, m);
        if (!contract_address) {
            return evmc::Result{contract_address.error()};
        }

        new_state.access_account(contract_address.value());

        evmc_message const m_call{
            .kind = EVMC_CALL,
            .depth = m.depth,
            .gas = m.gas,
            .recipient = contract_address.value(),
            .sender = m.sender,
            .value = m.value,
            .code_address = contract_address.value(),
        };

        evmc::Result result{transfer_call_balances(new_state, m_call)};

        if (result.status_code == EVMC_SUCCESS) {
            result = TInterpreter::execute(
                &new_host,
                m_call,
                byte_string_view(m.input_data, m.input_size));
        }

        if (result.status_code == EVMC_SUCCESS) {
            result = TTraits::deploy_contract_code(
                new_state, contract_address.value(), std::move(result));
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
        return {m};
    }

    static void transfer_balances(
        TState &s, evmc_message const &m, address_t const &to) noexcept
    {
        auto const value = intx::be::load<uint256_t>(m.value);
        s.subtract_from_balance(m.sender, value);
        s.add_to_balance(to, value);
    }

    [[nodiscard]] static std::optional<evmc_result>
    increment_sender_nonce(TState &s, evmc_message const &m) noexcept
    {
        auto const n = s.get_nonce(m.sender);
        if (n == std::numeric_limits<decltype(n)>::max()) {
            // Match geth behavior - don't overflow nonce
            return evmc_result{
                .status_code = EVMC_ARGUMENT_OUT_OF_RANGE, .gas_left = m.gas};
        }
        s.set_nonce(m.sender, n + 1);
        return std::nullopt;
    }

    [[nodiscard]] static auto
    create_new_contract(TState &s, address_t &new_address) noexcept
    {
        return [&](evmc_message const &m) {
            new_address = [&] {
                if (m.kind == EVMC_CREATE) {
                    return create_contract_address(
                        m.sender, s.get_nonce(m.sender) - 1); // YP Eqn. 85
                }
                else if (m.kind == EVMC_CREATE2) {
                    auto const code_hash =
                        ethash::keccak256(m.input_data, m.input_size);
                    return create2_contract_address(
                        m.sender, m.create2_salt, code_hash);
                }
                MONAD_ASSERT(false);
                return address_t{};
            }();

            // Prevent overwriting contracts - EIP-684
            if (s.account_exists(new_address)) {
                return result_t(
                    unexpected_t({.status_code = EVMC_INVALID_INSTRUCTION}));
            }

            s.create_account(new_address);

            return result_t({m});
        };
    }

    [[nodiscard]] static new_address_t
    make_account_address(TState &s, evmc_message const &m) noexcept
    {
        address_t new_address{};
        auto const result = check_sender_balance(s, m).and_then(
            create_new_contract(s, new_address));
        if (!result) {
            return unexpected_t{result.error()};
        }

        s.set_nonce(new_address, TTraits::starting_nonce());
        return {new_address};
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
