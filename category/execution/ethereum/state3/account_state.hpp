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
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/state3/account_substate.hpp>
#include <category/execution/ethereum/state3/version_stack.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

// TODO immer known to trigger incorrect warning
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#include <immer/map.hpp>
#pragma GCC diagnostic pop

#include <cstdint>
#include <limits>
#include <memory>
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

class AccountState
{
public: // TODO
    using StorageMap = immer::map<
        bytes32_t, bytes32_t, ankerl::unordered_dense::hash<monad::bytes32_t>>;

protected:
    std::optional<Account> account_{};

private:
    friend class State;
    friend class BlockState;
    friend class AccountHistory;
    friend struct trace::PrestateTracer;
    friend struct trace::StateDiffTracer;

public:
    StorageMap storage_{};

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

    [[nodiscard]] uint256_t get_balance() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->balance;
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
};

static_assert(sizeof(AccountState) == 104);

class CurrentAccountState final
    : public AccountState
    , public AccountSubstate
{
public:
    StorageMap transient_storage_{};

    explicit CurrentAccountState(std::optional<Account> &&account)
        : AccountState(std::move(account))
    {
    }

    explicit CurrentAccountState(std::optional<Account> const &account)
        : AccountState{account}
    {
    }

    explicit CurrentAccountState(AccountState const &account_state)
        : AccountState(account_state)
    {
    }

    CurrentAccountState(CurrentAccountState &&) noexcept = default;
    CurrentAccountState(CurrentAccountState const &) = default;
    CurrentAccountState &operator=(CurrentAccountState &&) noexcept = default;
    CurrentAccountState &operator=(CurrentAccountState const &) = default;

    bytes32_t get_transient_storage(bytes32_t const &key) const
    {
        if (auto const *const it = transient_storage_.find(key);
            MONAD_LIKELY(it)) {
            return *it;
        }
        return {};
    }

    void set_transient_storage(bytes32_t const &key, bytes32_t const &value)
    {
        transient_storage_ = transient_storage_.insert({key, value});
    }
};

static_assert(sizeof(CurrentAccountState) == 144);

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

    uint256_t get_balance_pessimistic()
    {
        set_validate_exact_balance();
        if (account_.has_value()) {
            return account_->balance;
        }
        return 0;
    }

    [[nodiscard]] uint256_t get_balance_or_zero() const
    {
        if (account_.has_value()) {
            return account_->balance;
        }
        return 0;
    }

private:
    friend class State;
    friend class AccountHistory;

    void set_min_balance(uint256_t const &value)
    {
        MONAD_ASSERT(account_.has_value());
        MONAD_ASSERT(account_->balance >= value);
        if (value > min_balance_) {
            min_balance_ = value;
        }
    }
};

class AccountHistory
{
    OriginalAccountState original_;
    std::optional<VersionStack<CurrentAccountState>> current_;

public:
    explicit AccountHistory(std::optional<Account> const &account)
        : original_(account)
    {
    }

    explicit AccountHistory(std::optional<Account> &&account)
        : original_(std::move(account))
    {
    }

    AccountHistory(AccountHistory &&) noexcept = default;
    AccountHistory(AccountHistory const &) = default;
    AccountHistory &operator=(AccountHistory &&) noexcept = default;
    AccountHistory &operator=(AccountHistory const &) = default;

    [[nodiscard]] OriginalAccountState const &original_state() const
    {
        return original_;
    }

    [[nodiscard]] bool has_current_state() const
    {
        return current_.has_value();
    }

    [[nodiscard]] VersionStack<CurrentAccountState> const &current_stack() const
    {
        MONAD_ASSERT(current_);
        return *current_;
    }

    [[nodiscard]] CurrentAccountState const &recent_current_state() const
    {
        MONAD_ASSERT(current_);
        return current_->recent();
    }

    [[nodiscard]] AccountState const &recent_state() const
    {
        if (current_) {
            return current_->recent();
        }
        return original_;
    }

public:
    // Access key: only State can construct this and call State-only APIs.
    class StateKey
    {
        friend class State;
        StateKey() = default;
    };

    [[nodiscard]] OriginalAccountState &original_state(StateKey)
    {
        return original_;
    }

    [[nodiscard]] VersionStack<CurrentAccountState> &current_stack(StateKey)
    {
        MONAD_ASSERT(current_);
        return *current_;
    }

    [[nodiscard]] CurrentAccountState &
    current_state(StateKey, unsigned const version)
    {
        if (!current_) {
            current_.emplace(CurrentAccountState{original_}, version);
        }
        return current_->current(version);
    }

    void add_to_balance(
        StateKey const key, unsigned const version,
        Incarnation const &incarnation, uint256_t const &delta)
    {
        auto &account_state = current_state(key, version);
        auto &account = account_state.account_;
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation};
        }

        MONAD_ASSERT_THROW(
            std::numeric_limits<uint256_t>::max() - delta >=
                account.value().balance,
            "balance overflow");

        account.value().balance += delta;
        account_state.touch();
    }

    void subtract_from_balance(
        StateKey const key, unsigned const version,
        Incarnation const &incarnation, uint256_t const &delta)
    {
        auto &account_state = current_state(key, version);
        auto &account = account_state.account_;
        if (MONAD_UNLIKELY(!account.has_value())) {
            account = Account{.incarnation = incarnation};
        }

        MONAD_ASSERT_THROW(
            delta <= account.value().balance, "balance underflow");

        account.value().balance -= delta;
        account_state.touch();
    }

    void pop_accept(StateKey, unsigned const version)
    {
        MONAD_ASSERT(current_);
        current_->pop_accept(version);
    }

    void pop_reject(StateKey, unsigned const version)
    {
        MONAD_ASSERT(current_);
        if (current_->pop_reject(version)) {
            current_.reset();
        }
    }

public:
    [[nodiscard]] uint256_t balance_with_exact_validation()
    {
        original_.set_validate_exact_balance();
        return recent_state().get_balance();
    }

    [[nodiscard]] uint256_t original_balance_pessimistic()
    {
        return original_.get_balance_pessimistic();
    }

    [[nodiscard]] bool record_min_balance_for_debit(uint256_t const &debit)
    {
        uint256_t const balance = recent_state().get_balance();
        if (balance >= debit) {
            uint256_t const diff = balance - debit;
            uint256_t const original_balance = original_.get_balance_or_zero();
            if (original_balance > diff) {
                original_.set_min_balance(original_balance - diff);
            }
            return true;
        }

        original_.set_validate_exact_balance();
        return false;
    }
};

MONAD_NAMESPACE_END
