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

// TODO immer known to trigger incorrect warning
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#include <immer/map.hpp>
#pragma GCC diagnostic pop

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
    using StorageMap = immer::map<
        bytes32_t, bytes32_t, ankerl::unordered_dense::hash<monad::bytes32_t>>;

protected:
    std::optional<Account> account_{};

private:
    friend class State;
    friend class BlockState;

    friend std::optional<Account> const &
    get_account_for_trace(AccountState const &as)
    {
        return as.account_;
    }

public:
    StorageMap storage_{};
    StorageMap transient_storage_{};

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

    AccountState(AccountState &&) noexcept = default;
    AccountState(AccountState const &) = default;
    AccountState &operator=(AccountState &&) noexcept = default;
    AccountState &operator=(AccountState const &) = default;

    [[nodiscard]] bool has_account() const
    {
        return account_.has_value();
    }

    [[nodiscard]] bytes32_t get_code_hash() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->code_hash;
        }
        return NULL_HASH;
    }

    [[nodiscard]] uint64_t get_nonce() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->nonce;
        }
        return 0;
    }

    [[nodiscard]] std::optional<Incarnation> get_incarnation() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->incarnation;
        }
        return std::nullopt;
    }

    bytes32_t get_transient_storage(bytes32_t const &key) const
    {
        if (auto const *const it = transient_storage_.find(key);
            MONAD_LIKELY(it)) {
            return *it;
        }
        return {};
    }

    evmc_storage_status set_storage(
        bytes32_t const &key, bytes32_t const &value,
        bytes32_t const &original_value)
    {
        bytes32_t current_value = original_value;
        {
            if (auto const *const it = storage_.find(key); it) {
                current_value = *it;
            }
        }
        if (value == bytes32_t{}) {
            return zero_out_key(key, original_value, current_value);
        }
        return set_current_value(key, value, original_value, current_value);
    }

    void set_transient_storage(bytes32_t const &key, bytes32_t const &value)
    {
        transient_storage_ = transient_storage_.insert({key, value});
    }
};

static_assert(sizeof(AccountState) == 144);

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

    bytes32_t get_balance_pessimistic()
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

public:
    bool record_balance_constraint_for_debit(uint256_t const &debit)
    {
        auto const balance = account_.has_value() ? account_->balance : 0;
        if (balance >= debit) {
            set_min_balance(debit);
            return true;
        }
        set_validate_exact_balance();
        return false;
    }

    bool record_balance_constraint_for_debit(uint512_t const &debit)
    {
        if (debit > uint512_t{std::numeric_limits<uint256_t>::max()}) {
            set_validate_exact_balance();
            return false;
        }
        return record_balance_constraint_for_debit(
            static_cast<uint256_t>(debit));
    }
};

MONAD_NAMESPACE_END
