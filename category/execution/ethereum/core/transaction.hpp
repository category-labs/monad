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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
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
    LAST,
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

struct Transaction
{
    SignatureAndChain sc{};
    uint64_t nonce{};
    uint256_t max_fee_per_gas{}; // gas_price
    uint64_t gas_limit{};
    uint256_t value{};
    std::optional<Address> to{};
    TransactionType type{};
    byte_string data{};
    AccessList access_list{};
    uint256_t max_priority_fee_per_gas{};
    uint256_t max_fee_per_blob_gas{};
    std::vector<bytes32_t> blob_versioned_hashes{};

    friend bool operator==(Transaction const &, Transaction const &) = default;
};

static_assert(sizeof(Transaction) == 360);
static_assert(alignof(Transaction) == 8);

std::optional<Address> recover_sender(Transaction const &);

MONAD_NAMESPACE_END
