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
    class TStaticPrecompiles>
struct Evm
{
    using result_t = tl::expected<evmc_message, evmc_result>;
    using new_address_t = tl::expected<address_t, evmc_result>;
    using unexpected_t = tl::unexpected<evmc_result>;

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result create_contract_account(
        TEvmHost *, TState &state, evmc_message const &m) noexcept
    {
        auto const contract_address = make_account_address(state, m);
        if (!contract_address) {
            return evmc::Result{contract_address.error()};
        }
        // evmone execute, just this for now
        evmc_result res = {.status_code = EVMC_SUCCESS, .gas_left = 12'000};

        if (!TTraits::store_contract_code(
                state, contract_address.value(), res)) {
            state.revert();
        }

        return evmc::Result{res};
    }

    template <class TEvmHost>
    [[nodiscard]] static evmc::Result
    call_evm(TEvmHost *, TState &state, evmc_message const &m) noexcept
    {
        if (auto const result = transfer_call_balances(state, m);
            result.status_code != EVMC_SUCCESS) {
            return evmc::Result{result};
        }
        evmc_result const result =
            TStaticPrecompiles::static_precompile_exec_func(m.code_address)
                .transform([&](auto static_precompile_execute) {
                    return static_precompile_execute(m);
                })
                // execute on backend, just this for now
                .value_or(evmc_result{
                    .status_code = EVMC_SUCCESS, .gas_left = m.gas});

        if (result.status_code == EVMC_REVERT) {
            state.revert();
        }

        return evmc::Result{result};
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
        auto const to_balance = intx::be::load<uint256_t>(s.get_balance(to));
        s.set_balance(m.sender, from_balance - value);
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
                        m.sender, s.get_nonce(m.sender));
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

            s.create_contract(new_address);

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
        transfer_balances(s, m, new_address);
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
