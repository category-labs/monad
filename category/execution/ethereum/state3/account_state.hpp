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
#include <category/execution/ethereum/state3/page_tracker.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;
class BlockState;

namespace trace
{
    struct PrestateTracer;
    struct StateDiffTracer;
}

// Mutable slots with linear lookup; undo records save only written slots.
// Appending preserves indices, but reallocation can invalidate pointers
// and erase can move the last entry.
class FlatStorage
{
    std::vector<std::pair<bytes32_t, bytes32_t>> v_{};

public:
    [[nodiscard]] bytes32_t const *find(bytes32_t const &key) const
    {
        for (auto const &e : v_) {
            if (__builtin_memcmp(e.first.bytes, key.bytes, sizeof(key.bytes)) ==
                0) {
                return &e.second;
            }
        }
        return nullptr;
    }

    void upsert(bytes32_t const &key, bytes32_t const &value)
    {
        for (auto &e : v_) {
            if (__builtin_memcmp(e.first.bytes, key.bytes, sizeof(key.bytes)) ==
                0) {
                e.second = value;
                return;
            }
        }
        v_.emplace_back(key, value);
    }

    // Restore absence after a reverted insertion: keeping the original value
    // here would still include the slot in the commit set.
    void erase(bytes32_t const &key)
    {
        for (auto &e : v_) {
            if (__builtin_memcmp(e.first.bytes, key.bytes, sizeof(key.bytes)) ==
                0) {
                e = v_.back();
                v_.pop_back();
                return;
            }
        }
    }

    [[nodiscard]] bool empty() const
    {
        return v_.empty();
    }

    [[nodiscard]] std::size_t size() const
    {
        return v_.size();
    }

    [[nodiscard]] auto begin() const
    {
        return v_.begin();
    }

    [[nodiscard]] auto end() const
    {
        return v_.end();
    }
};

class AccountState : public AccountSubstate
{
public: // TODO
    using StorageMap = FlatStorage;

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
    PageTracker page_tracker_{};

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
        transient_storage_.upsert(key, value);
    }
};

// Guard against unintended growth of the per-account state.
static_assert(sizeof(AccountState) == 184);

// RELAXED MERGE
// track the min original balance needed at start of transaction and if the
// original and current balances can be adjusted
// Cache original slot values on first read; entries are never overwritten
// or rolled back. Append-only storage preserves indices, though vector
// reallocation may invalidate pointers. Lookup uses a linear scan.
class PrestateStorage
{
    // [(slot identifier, original value)]
    std::vector<std::pair<bytes32_t, bytes32_t>> v_{};

public:
    bytes32_t const *find(bytes32_t const &k) const
    {
        for (auto const &e : v_) {
            if (__builtin_memcmp(e.first.bytes, k.bytes, sizeof(k.bytes)) == 0) {
                return &e.second;
            }
        }
        return nullptr;
    }

    void insert(bytes32_t const &k, bytes32_t const &v)
    {
        v_.emplace_back(k, v);
    }

    bool empty() const
    {
        return v_.empty();
    }

    std::size_t size() const
    {
        return v_.size();
    }
    auto begin() const { return v_.begin(); }
    auto end() const { return v_.end(); }
};

class OriginalAccountState final : public AccountState
{
    bool validate_exact_balance_{false};
    uint256_t min_balance_{0};

public:
    // Original slot values; replaces the inherited storage_, left unused here.
    PrestateStorage prestate_storage_{};

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

    uint256_t get_balance_pessimistic()
    {
        set_validate_exact_balance();
        if (account_.has_value()) {
            return account_->balance;
        }
        return 0;
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
