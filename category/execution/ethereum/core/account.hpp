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

struct Account
{
    uint256_t balance{0}; // sigma[a]_b
    bytes32_t code_hash{NULL_HASH}; // sigma[a]_c
    uint64_t nonce{0}; // sigma[a]_n
    Incarnation incarnation{0, 0};

    friend bool operator==(Account const &, Account const &) = default;
};

static_assert(sizeof(Account) == 80);
static_assert(alignof(Account) == 8);

static_assert(sizeof(std::optional<Account>) == 88);
static_assert(alignof(std::optional<Account>) == 8);

// YP (14)
inline constexpr bool is_empty(Account const &account)
{
    return account.code_hash == NULL_HASH && account.nonce == 0 &&
           account.balance == 0;
}

// YP (15)
inline constexpr bool is_dead(std::optional<Account> const &account)
{
    return !account.has_value() || is_empty(account.value());
}

MONAD_NAMESPACE_END
