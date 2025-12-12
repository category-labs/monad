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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

class Account
{
    uint256_t balance{0}; // sigma[a]_b

public:
    bytes32_t code_hash{NULL_HASH}; // sigma[a]_c
    uint64_t nonce{0}; // sigma[a]_n
    Incarnation incarnation{0, 0};

    friend bool operator==(Account const &, Account const &) = default;

    explicit Account(
        uint256_t const &initial_balance = 0,
        bytes32_t const &initial_code_hash = NULL_HASH,
        uint64_t initial_nonce = 0,
        Incarnation const &initial_incarnation = Incarnation{0, 0})
        : balance{initial_balance}
        , code_hash{initial_code_hash}
        , nonce{initial_nonce}
        , incarnation{initial_incarnation}
    {
    }

    /// Relaxed merge validation:
    ///  Use this function only if there are no dependencies on the
    ///  returned value that may affect transaction merge validation. Otherwise
    ///  use 'ConstBalanceAccessor' to set the proper requirements for merge
    ///  validation.
    uint256_t const &get_balance_unsafe() const
    {
        return balance;
    }

    void set_balance(uint256_t const &new_balance)
    {
        balance = new_balance;
    }

    void add_to_balance(uint256_t const &amount)
    {
        balance += amount;
    }

    /// The same warning for 'get_balance_unsafe' applies here.
    void subtract_from_balance_unsafe(uint256_t const &amount)
    {
        MONAD_ASSERT(amount <= balance);
        balance -= amount;
    }

    bool is_empty() const
    {
        return code_hash == NULL_HASH && nonce == 0 && balance == 0;
    }
};

static_assert(sizeof(Account) == 80);
static_assert(alignof(Account) == 8);

static_assert(sizeof(std::optional<Account>) == 88);
static_assert(alignof(std::optional<Account>) == 8);

// YP (14)
inline constexpr bool is_empty(Account const &account)
{
    return account.is_empty();
}

// YP (15)
inline constexpr bool is_dead(std::optional<Account> const &account)
{
    return !account.has_value() || is_empty(account.value());
}

MONAD_NAMESPACE_END
