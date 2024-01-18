#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/state3/account_substate.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

class AccountState final : public AccountSubstate
{
public: // TODO
    template <class Key, class T>
    using Map = ankerl::unordered_dense::segmented_map<Key, T>;

    std::optional<Account> account_{};
    Map<bytes32_t, bytes32_t> storage_{};

    evmc_storage_status zero_out_key(
        bytes32_t const &key, bytes32_t const &original_value,
        bytes32_t const &current_value);

    evmc_storage_status set_current_value(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value, bytes32_t const &current_value);

public:
    explicit AccountState(std::optional<Account> &&account)
        : account_{std::move(account)}
    {
    }

    explicit AccountState(std::optional<Account> const &account)
        : account_{account}
    {
    }

    AccountState(AccountState &&) = default;
    AccountState(AccountState const &) = default;
    AccountState &operator=(AccountState &&) = default;
    AccountState &operator=(AccountState const &) = default;

    constexpr bool account_exists() const noexcept
    {
        return account_.has_value();
    }

    constexpr uint64_t get_nonce() const noexcept
    {
        if (MONAD_LIKELY(account_)) {
            return account_->nonce;
        }
        return 0;
    }

    constexpr bytes32_t get_balance() const noexcept
    {
        if (MONAD_LIKELY(account_)) {
            return intx::be::store<bytes32_t>(account_->balance);
        }
        return {};
    }

    constexpr bytes32_t get_code_hash() const noexcept
    {
        if (MONAD_LIKELY(account_)) {
            return account_->code_hash;
        }
        return NULL_HASH;
    }

    constexpr uint64_t get_incarnation() const noexcept
    {
        if (MONAD_LIKELY(account_)) {
            return account_->incarnation;
        }
        return 0;
    }

    std::optional<bytes32_t> get_storage(bytes32_t const &key) const
    {
        auto const it = storage_.find(key);
        if (MONAD_LIKELY(it != storage_.end())) {
            return it->second;
        }
        return {};
    }

    void set_nonce(uint64_t const nonce)
    {
        MONAD_ASSERT(account_);

        account_->nonce = nonce;
    }

    void add_to_balance(uint256_t const &delta)
    {
        if (MONAD_UNLIKELY(!account_)) {
            account_ = Account{};
        }

        MONAD_ASSERT(UINT256_MAX - delta >= account_->balance);

        account_->balance += delta;
        touch();
    }

    void subtract_from_balance(uint256_t const &delta)
    {
        if (MONAD_UNLIKELY(!account_)) {
            account_ = Account{};
        }

        MONAD_ASSERT(delta <= account_->balance);

        account_->balance -= delta;
        touch();
    }

    void set_code_hash(bytes32_t const &code_hash)
    {
        MONAD_ASSERT(account_);

        account_->code_hash = code_hash;
    }

    evmc_storage_status set_storage(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value)
    {
        bytes32_t current_value = original_value;
        {
            auto const it = storage_.find(key);
            if (it != storage_.end()) {
                current_value = it->second;
            }
        }
        if (value == bytes32_t{}) {
            return zero_out_key(key, original_value, current_value);
        }
        return set_current_value(key, value, original_value, current_value);
    }
};

MONAD_NAMESPACE_END
