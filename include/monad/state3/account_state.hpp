#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/account_substate.hpp>

#include <ethash/keccak.hpp>

#include <intx/intx.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

class AccountState final : public AccountSubstate
{
    Address const address_{};
    BlockState &block_state_;
    StateDelta state_delta_{};

public:
    explicit AccountState(Address const &, BlockState &);

    AccountState(AccountState &&) = default;
    AccountState(AccountState const &) = default;
    AccountState &operator=(AccountState &&) = delete;
    AccountState &operator=(AccountState const &) = delete;

protected:
    Address const &get_address() const
    {
        return address_;
    }

    std::optional<Account> const &get_account() const
    {
        return state_delta_.account.second;
    }

    std::optional<Account> &get_account()
    {
        return state_delta_.account.second;
    }

    Delta<bytes32_t> &read_storage_delta(bytes32_t const &location)
    {
        {
            auto const it = state_delta_.storage.find(location);
            if (MONAD_LIKELY(it != state_delta_.storage.end())) {
                return it->second;
            }
        }
        auto const &account = get_account();
        MONAD_ASSERT(account.has_value());
        uint64_t const incarnation = account.value().incarnation;
        auto const result =
            block_state_.read_storage(address_, incarnation, location);
        auto const it =
            state_delta_.storage.try_emplace(location, result, result).first;
        return it->second;
    }

public:
    bytes32_t get_balance() const
    {
        auto const &account = get_account();
        if (MONAD_LIKELY(account.has_value())) {
            return intx::be::store<bytes32_t>(account.value().balance);
        }
        return {};
    }

    bytes32_t get_code_hash() const
    {
        auto const &account = get_account();
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().code_hash;
        }
        return NULL_HASH;
    }

    uint64_t get_nonce() const
    {
        auto const &account = get_account();
        if (MONAD_LIKELY(account.has_value())) {
            return account.value().nonce;
        }
        return 0;
    }

    void add_to_balance(uint256_t const &delta)
    {
        auto &account = get_account();
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{};
        }

        MONAD_ASSERT(
            std::numeric_limits<uint256_t>::max() - delta >=
            account.value().balance);

        account.value().balance += delta;
        touch();
    }

    void subtract_from_balance(uint256_t const &delta)
    {
        auto &account = get_account();
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{};
        }

        MONAD_ASSERT(delta <= account.value().balance);

        account.value().balance -= delta;
        touch();
    }

    void set_code(byte_string_view const &code)
    {
        auto const code_hash = std::bit_cast<bytes32_t>(
            ethash::keccak256(code.data(), code.size()));

        auto &account = get_account();
        MONAD_ASSERT(account.has_value());
        account.value().code_hash = code_hash;
        if (!code.empty()) {
            // TODO
            // read_code(code_hash) = code;
        }
    }
};

MONAD_NAMESPACE_END
