#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/create_contract_address.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <tl/expected.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <
    class TState, concepts::fork_traits<TState> TTraits,
    class TStaticPrecompiles, class TInterpreter>
struct Evm
{
    using result_t = tl::expected<evmc_message, evmc_result>;
    using new_address_t = tl::expected<address_t, evmc_result>;
    using unexpected_t = tl::unexpected<evmc_result>;

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result create_contract_account(
        TEvmHost *host, TState &state, evmc_message const &m) noexcept
    {
        auto const contract_address = make_account_address(state, m);
        if (!contract_address) {
            return evmc::Result{contract_address.error()};
        }

        byte_string code{m.input_data, m.input_size};

        auto execute_init_code = [&]() {
            evmc_message m_call{
                .kind = EVMC_CALL,
                .depth = m.depth,
                .gas = m.gas,
                .recipient = contract_address.value(),
                .sender = m.sender,
                .value = m.value,
                .code_address = contract_address.value(),
            };

            if (auto const transfer_result =
                    transfer_call_balances(state, m_call);
                transfer_result.status_code != EVMC_SUCCESS) {
                return evmc::Result{transfer_result};
            }

            return TInterpreter::execute(
                host, m_call, byte_string_view(m.input_data, m.input_size));
        };

        auto deploy_code = [&](auto &&result) {
            if (result.status_code == EVMC_SUCCESS) {
                return TTraits::deploy_contract_code(
                    state, contract_address.value(), std::move(result));
            }
            return std::forward<decltype(result)>(result);
        };

        auto deploy_result = deploy_code(execute_init_code());

        if (deploy_result.status_code != EVMC_SUCCESS) {
            state.revert();
        }

        return deploy_result;
    }

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result
    call_evm(TEvmHost *host, TState &state, evmc_message const &m) noexcept
    {
        if (auto const result = transfer_call_balances(state, m);
            result.status_code != EVMC_SUCCESS) {
            return evmc::Result{result};
        }
        evmc::Result result =
            TStaticPrecompiles::static_precompile_exec_func(m.code_address)
                .transform([&](auto static_precompile_execute) {
                    return static_precompile_execute(m);
                })
                .or_else([&] {
                    auto const code =
                        state.get_code(state.get_code_hash(m.code_address));
                    return TInterpreter::execute(host, m, code);
                })
                .value();

        if (result.status_code != EVMC_SUCCESS) {
            state.revert();
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
        auto const from_balance =
            intx::be::load<uint256_t>(s.get_balance(m.sender));
        s.set_balance(m.sender, from_balance - value);
        auto const to_balance = intx::be::load<uint256_t>(s.get_balance(to));
        s.set_balance(to, to_balance + value);
    }

    [[nodiscard]] static auto increment_sender_nonce(TState &s) noexcept
    {
        return [&](evmc_message const &m) {
            auto const n = s.get_nonce(m.sender) + 1;
            if (s.get_nonce(m.sender) > n) {
                // Match geth behavior - don't overflow nonce
                return result_t(unexpected_t(
                    {.status_code = EVMC_ARGUMENT_OUT_OF_RANGE,
                     .gas_left = m.gas}));
            }
            s.set_nonce(m.sender, n);
            return result_t({m});
        };
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
        auto const result = check_sender_balance(s, m)
                                .and_then(increment_sender_nonce(s))
                                .and_then(create_new_contract(s, new_address));
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
                if (!s.account_exists(m.recipient)) {
                    s.create_account(m.recipient);
                }
                transfer_balances(s, m, m.recipient);
            }
        }
        return {.status_code = EVMC_SUCCESS};
    }
};

MONAD_EXECUTION_NAMESPACE_END
