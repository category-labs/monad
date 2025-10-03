// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/state3/account_substate.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

class State;
class BlockState;

namespace trace
{
    struct PrestateTracer;
    struct StateDiffTracer;
}

class AccountState : public AccountSubstate
{
public: // TODO
    template <class Key, class T>
    using Map = ankerl::unordered_dense::segmented_map<Key, T>;

protected:
    std::optional<Account> account_{};

private:
    friend class State;
    friend class BlockState;

    // the classes below can access the account_ field just for logging but
    // CANNOT use it to make decisions affecting the final state (state of
    // accounts) of execution.
    friend struct trace::PrestateTracer;
    friend struct trace::StateDiffTracer;

public:
    Map<bytes32_t, bytes32_t> storage_{};
    Map<bytes32_t, bytes32_t> transient_storage_{};

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

    [[nodiscard]] bool has_account() const
    {
        return account_.has_value();
    }

    [[nodiscard]] bytes32_t get_code_hash() const
    {
        if (account_.has_value()) {
            return account_->code_hash;
        }
        return NULL_HASH;
    }

    [[nodiscard]] uint64_t get_nonce() const
    {
        if (account_.has_value()) {
            return account_->nonce;
        }
        return 0;
    }

    [[nodiscard]] std::optional<Incarnation> get_incarnation() const
    {
        if (account_.has_value()) {
            return account_->incarnation;
        }
        return std::nullopt;
    }

    bytes32_t get_transient_storage(bytes32_t const &key) const
    {
        auto const it = transient_storage_.find(key);
        if (MONAD_LIKELY(it != transient_storage_.end())) {
            return it->second;
        }
        return {};
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

    void set_transient_storage(bytes32_t const &key, bytes32_t const &value)
    {
        transient_storage_[key] = value;
    }
};

// RELAXED MERGE
// track the min original balance needed at start of transaction and if the
// original and current balances can be adjusted
class OriginalAccountState final : public AccountState
{
    bool validate_exact_balance_{false};
    uint256_t min_balance_{0};

public:
    explicit OriginalAccountState(std::optional<Account> &&account)
        : AccountState(std::move(account))
    {
    }

    explicit OriginalAccountState(std::optional<Account> const &account)
        : AccountState{account}
    {
    }

    [[nodiscard]] bool validate_exact_balance() const
    {
        return validate_exact_balance_;
    }

    [[nodiscard]] uint256_t const &min_balance() const
    {
        return min_balance_;
    }

    void set_validate_exact_balance()
    {
        validate_exact_balance_ = true;
    }

    bytes32_t get_balance()
    {
        set_validate_exact_balance();
        if (account_.has_value()) {
            return intx::be::store<bytes32_t>(account_->balance);
        }
        return {};
    }

private:
    friend class State;

    void set_min_balance(uint256_t const &value)
    {
        MONAD_ASSERT(account_.has_value());
        MONAD_ASSERT(account_->balance >= value);
        if (value > min_balance_) {
            min_balance_ = value;
        }
    }
};

MONAD_NAMESPACE_END
