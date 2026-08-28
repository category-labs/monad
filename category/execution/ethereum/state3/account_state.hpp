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

// The slots a row holds. This was immer::map. A persistent map bought an O(1) copy of the row when
// a frame opened; the undo log does not need that copy -- it journals the slots a frame actually
// WRITES, and a frame writes two of the thirty a row holds.
//
// Unsorted, and deliberately: insertion appends, so it never moves an existing entry and an index
// into this vector stays valid. Sorting it would memmove the tail on every insert to save a handful
// of 32-byte compares. Same reasoning, and the same measurement, that put a vector under A_K.
class FlatStorage
{
    std::vector<std::pair<bytes32_t, bytes32_t>> v_{};

public:
    [[nodiscard]] bytes32_t const *find(bytes32_t const &key) const
    {
        std::uint64_t const tail = key_tail(key);
        for (auto const &e : v_) {
            if (key_equals(key, tail, e.first)) {
                return &e.second;
            }
        }
        return nullptr;
    }

    void upsert(bytes32_t const &key, bytes32_t const &value)
    {
        std::uint64_t const tail = key_tail(key);
        for (auto &e : v_) {
            if (key_equals(key, tail, e.first)) {
                e.second = value;
                return;
            }
        }
        v_.emplace_back(key, value);
    }

    // Removing a slot restores "absent", which is not the same as present-and-equal-to-pre-state:
    // BlockState commits every slot the overlay lists, so a slot left behind by a reverted write
    // would join the commit set.
    void erase(bytes32_t const &key)
    {
        std::uint64_t const tail = key_tail(key);
        for (auto &e : v_) {
            if (key_equals(key, tail, e.first)) {
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

class OriginalAccountState;

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

    // The row in original_ this one was created from, or null on an original row. A storage read
    // that misses the overlay needs the pre-state row, and finding it by address hashed the same
    // 20 bytes a second time: get_storage runs 5,184 times a block at 187 steps, and two of those
    // lookups are the same lookup.
    //
    // Safe to hold because original_ is a segmented map that is only ever inserted into -- one
    // try_emplace, no erase, no clear -- so an element never moves for the life of the block.
    // current_ IS erased, in pop_reject, but that erases the row holding the pointer, not its
    // target.
    OriginalAccountState *orig_{nullptr};

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

// Kept exact so unintended growth fails the build. The undo log copies this row once per frame per
// account -- everything but its storage_, which is journalled per slot -- so its size is a cost, not
// a detail.
//
// 16 wider than the two persistent handles it replaced, not 32: the second vector lands in padding
// the row already carried, so the number is not the arithmetic and has to be read off the compiler.
static_assert(sizeof(AccountState) == 192);

// RELAXED MERGE
// track the min original balance needed at start of transaction and if the
// original and current balances can be adjusted
// The ORIGINAL row's slot cache: pre-state values the block has read. Monotone by construction --
// inserted once per slot on first read, never overwritten, and never rolled back, because
// original_ sits outside revert semantics entirely (find and try_emplace are the only operations
// on it, and set_original_nonce / set_min_balance are deliberately not journalled). That is what
// lets it flatten with NO journal at all, ahead of the current overlay which needs one.
//
// Unsorted with a linear scan, not sorted: insertion is append-only and never moves an existing
// entry, so an index into it stays valid -- which is what the row work above this will want. A
// sorted vector would memmove ~1 kB per insert to save a handful of compares.
class PrestateStorage
{
    std::vector<std::pair<bytes32_t, bytes32_t>> v_{};

public:
    bytes32_t const *find(bytes32_t const &k) const
    {
        std::uint64_t const tail = key_tail(k);
        for (auto const &e : v_) {
            if (key_equals(k, tail, e.first)) {
                return &e.second;
            }
        }
        return nullptr;
    }

    void insert(bytes32_t const &k, bytes32_t const &v)
    {
        v_.emplace_back(k, v);
    }

    bool empty() const { return v_.empty(); }
    std::size_t size() const { return v_.size(); }
    auto begin() const { return v_.begin(); }
    auto end() const { return v_.end(); }
};

class OriginalAccountState final : public AccountState
{
    bool validate_exact_balance_{false};
    uint256_t min_balance_{0};

public:
    // The base's storage_ is unused for an original row: this replaces it. Both are flat vectors
    // now, so the two could be one member -- what keeps them apart is the contract. This one is
    // append-only and never overwrites, which is why it needs no journal; the base's is a mutable
    // overlay with erase(). Merging them would hand an original row operations it must never use.
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
