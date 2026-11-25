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

#include <category/core/config.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <algorithm>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class TransactionType : char
{
    legacy = 0,
    eip2930,
    eip1559,
    eip4844,
    eip7702,
    LAST,
    monad = 0x40,
};

struct AccessEntry
{
    Address a{};
    std::vector<bytes32_t> keys{};

    friend bool operator==(AccessEntry const &, AccessEntry const &) = default;
};

static_assert(sizeof(AccessEntry) == 48);
static_assert(alignof(AccessEntry) == 8);

using AccessList = std::vector<AccessEntry>;

static_assert(sizeof(AccessList) == 24);
static_assert(alignof(AccessList) == 8);

struct AuthorizationEntry
{
    SignatureAndChain sc{};
    Address address{};
    uint64_t nonce{};

    friend bool operator==(
        AuthorizationEntry const &, AuthorizationEntry const &) = default;
};

static_assert(sizeof(AuthorizationEntry) == 144);
static_assert(alignof(AuthorizationEntry) == 8);

std::optional<Address> recover_authority(AuthorizationEntry const &);

using AuthorizationList = std::vector<AuthorizationEntry>;

static_assert(sizeof(AuthorizationList) == 24);
static_assert(alignof(AuthorizationList) == 8);

inline constexpr uint8_t MONAD_CALLS_FEATURE = 0x08;
inline constexpr uint64_t MONAD_CALL_ENTRY_GAS = 21'000;

struct TransactionCall
{
    std::optional<Address> to{};
    uint256_t value{};
    byte_string data{};

    friend bool
    operator==(TransactionCall const &, TransactionCall const &) = default;
};

struct Transaction
{
    SignatureAndChain sc{};
    uint64_t nonce{};
    uint256_t max_fee_per_gas{}; // gas_price
    uint64_t gas_limit{};
    uint256_t value{};
    std::optional<Address> to{};
    TransactionType type{};
    // Feature presence is part of the canonical transaction commitment.
    bool monad_access_list_present{};
    byte_string data{};
    AccessList access_list{};
    uint256_t max_priority_fee_per_gas{};
    uint256_t max_fee_per_blob_gas{};
    std::vector<bytes32_t> blob_versioned_hashes{};
    AuthorizationList authorization_list{};
    // Complete signed CALLS payload, including entries not reached in
    // execution. A one-entry batch remains distinct from the scalar CALL
    // feature.
    std::optional<std::vector<TransactionCall>> calls{};

    constexpr bool is_batch() const noexcept
    {
        return calls.has_value();
    }

    constexpr bool is_create() const noexcept
    {
        return calls ? (!calls->empty() && !calls->front().to) : !to;
    }

    friend bool operator==(Transaction const &, Transaction const &) = default;
};

static_assert(sizeof(Transaction) == 416);
static_assert(alignof(Transaction) == 8);

std::optional<Address> recover_sender(Transaction const &);

MONAD_NAMESPACE_END
