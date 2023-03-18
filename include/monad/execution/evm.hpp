#pragma once

#include <monad/core/concepts.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/create_contract_address.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <tl/expected.hpp>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TState, concepts::fork_traits<TState> TTraits>
struct Evm
{
    TState &state_;
    address_t new_address_{};

    using result_t = tl::expected<evmc_message, evmc_result>;
    using new_address_t = tl::expected<address_t, evmc_result>;
    using unexpected_t = tl::unexpected<evmc_result>;

    Evm(TState &s)
        : state_{s}
    {
    }

    [[nodiscard]] result_t check_sender_balance(evmc_message const &m) noexcept
    {
        auto const value = intx::be::load<uint256_t>(m.value);
        auto const balance =
            intx::be::load<uint256_t>(state_.get_balance(m.sender));
        if (balance < value) {
            return unexpected_t(
                {.status_code = EVMC_INSUFFICIENT_BALANCE, .gas_left = m.gas});
        }
        return {m};
    }

    inline void
    transfer_balances(evmc_message const &m, address_t const &to) noexcept
    {
        auto const value = intx::be::load<uint256_t>(m.value);
        auto balance = intx::be::load<uint256_t>(state_.get_balance(m.sender));
        state_.set_balance(m.sender, balance - value);
        balance = intx::be::load<uint256_t>(state_.get_balance(to));
        state_.set_balance(to, balance + value);
    }

    [[nodiscard]] inline result_t
    increment_sender_nonce(evmc_message const &m) noexcept
    {
        auto const n = state_.get_nonce(m.sender) + 1;
        if (state_.get_nonce(m.sender) > n) {
            // Match geth behavior - don't overflow nonce
            return unexpected_t(
                {.status_code = EVMC_ARGUMENT_OUT_OF_RANGE, .gas_left = m.gas});
        }
        state_.set_nonce(m.sender, n);
        return {m};
    }

    [[nodiscard]] inline result_t
    create_new_contract(evmc_message const &m) noexcept
    {
        new_address_ = [&] {
            if (m.kind == EVMC_CREATE) {
                return create_contract_address(
                    m.sender, state_.get_nonce(m.sender));
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
        if (state_.get_nonce(new_address_) != 0 ||
            state_.get_code_hash(new_address_) != NULL_HASH) {
            return unexpected_t({.status_code = EVMC_INVALID_INSTRUCTION});
        }

        state_.create_contract(new_address_);

        return {m};
    }

    [[nodiscard]] new_address_t
    make_account_address(evmc_message const &m) noexcept
    {
        auto const result =
            check_sender_balance(m)
                .and_then([&](auto x) { return increment_sender_nonce(x); })
                .and_then([&](auto x) { return create_new_contract(x); });
        if (!result) {
            return unexpected_t{result.error()};
        }

        state_.set_nonce(new_address_, TTraits::starting_nonce());
        transfer_balances(m, new_address_);
        return {new_address_};
    }

    [[nodiscard]] evmc_result transfer_call_balances(evmc_message const &m)
    {
        if (m.kind != EVMC_DELEGATECALL) {
            if (auto const result = check_sender_balance(m);
                !result.has_value()) {
                return result.error();
            }
            else if (m.flags != EVMC_STATIC) {
                transfer_balances(m, m.recipient);
            }
        }
        return {.status_code = EVMC_SUCCESS};
    }
};

MONAD_EXECUTION_NAMESPACE_END
