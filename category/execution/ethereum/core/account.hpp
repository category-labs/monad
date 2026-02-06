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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

class CodeStorage
{
    byte_string data_{};

public:
    static constexpr unsigned DELEGATED_CODE_SIZE = 23;

    CodeStorage() = default;

    // NOLINTNEXTLINE(google-explicit-constructor)
    CodeStorage(byte_string const &code_or_hash)
        : data_(code_or_hash)
    {
        MONAD_ASSERT(byte_string_view{code_or_hash} != NULL_HASH);
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    CodeStorage(byte_string_view const code_or_hash)
        : data_(code_or_hash)
    {
        MONAD_ASSERT(code_or_hash != NULL_HASH);
    }

    // NOLINTNEXTLINE(google-explicit-constructor)
    CodeStorage(bytes32_t const &hash)
        : data_(hash == NULL_HASH ? byte_string{} : to_byte_string(hash))
    {
    }

    friend bool operator==(CodeStorage const &, CodeStorage const &) = default;

    size_t size() const noexcept
    {
        return data_.size();
    }

    bool is_hash() const noexcept
    {
        return data_.size() == sizeof(bytes32_t);
    }

    bool inline_delegated_code() const noexcept
    {
        return data_.size() == DELEGATED_CODE_SIZE;
    }

    bytes32_t get_hash() const
    {
        if (data_.empty()) {
            return NULL_HASH;
        }
        if (is_hash()) {
            return to_bytes(data_);
        }
        MONAD_ASSERT(data_.size() == DELEGATED_CODE_SIZE);
        return to_bytes(keccak256(data_));
    }

    byte_string_view as_view() const noexcept
    {
        return byte_string_view{data_};
    }
};

static_assert(sizeof(CodeStorage) == 32);
static_assert(alignof(CodeStorage) == 8);

struct Account
{
    uint256_t balance{0}; // sigma[a]_b
    CodeStorage code_or_hash{}; // sigma[a]_c
    uint64_t nonce{0}; // sigma[a]_n
    Incarnation incarnation{0, 0};

    friend bool operator==(Account const &, Account const &) = default;

    byte_string_view code_view() const noexcept
    {
        return code_or_hash.as_view();
    }

    bool has_code() const noexcept
    {
        return !code_or_hash.as_view().empty();
    }

    // Returns true if this is a delegated account using the new format,
    // where the delegated code is stored inline in the Account itself.
    // Legacy delegated accounts always return false (no inline code).
    bool inline_delegated_code() const noexcept
    {
        return code_or_hash.inline_delegated_code();
    }

    bytes32_t get_code_hash() const
    {
        return code_or_hash.get_hash();
    }
};

static_assert(sizeof(Account) == 80);
static_assert(alignof(Account) == 8);

static_assert(sizeof(std::optional<Account>) == 88);
static_assert(alignof(std::optional<Account>) == 8);

// YP (14)
inline constexpr bool is_empty(Account const &account)
{
    return !account.has_code() && account.nonce == 0 && account.balance == 0;
}

// YP (15)
inline constexpr bool is_dead(std::optional<Account> const &account)
{
    return !account.has_value() || is_empty(account.value());
}

MONAD_NAMESPACE_END
