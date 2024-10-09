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

    ////////////////////////

    constexpr bool exists() const
    {
        return account_.has_value();
    }

    constexpr bool is_dead() const
    {
        return ::monad::is_dead(account_);
    }

    constexpr uint64_t get_nonce() const
    {
        if (MONAD_UNLIKELY(!account_)) {
            return 0;
        }
        return account_->nonce;
    }

    constexpr bytes32_t get_balance() const
    {
        if (MONAD_UNLIKELY(!account_)) {
            return {};
        }
        return intx::be::store<bytes32_t>(account_->balance);
    }

    constexpr bytes32_t get_code_hash() const
    {
        if (MONAD_UNLIKELY(!account_)) {
            return NULL_HASH;
        }
        return account_->code_hash;
    }

    ////////////////////////

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
