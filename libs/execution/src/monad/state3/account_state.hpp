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

    bool match_nonce_{false};
    bool match_balance_{false};
    uint64_t match_tx_nonce_{0};
    uint256_t min_balance_{0};

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

    bool match_nonce() const
    {
        return match_nonce_;
    }

    bool match_balance() const
    {
        return match_balance_;
    }

    uint64_t match_tx_nonce() const
    {
        return match_tx_nonce_;
    }

    uint256_t const &min_balance() const
    {
        return min_balance_;
    }

    void set_match_nonce()
    {
        match_nonce_ = true;
    }

    void set_match_balance()
    {
        match_balance_ = true;
    }

    void set_match_tx_nonce(uint64_t tx_nonce)
    {
        match_tx_nonce_ = tx_nonce;
    }

    void add_to_min_balance(uint256_t const &delta)
    {
        min_balance_ += delta;
    }
};

MONAD_NAMESPACE_END
