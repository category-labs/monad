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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/vm/vm.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <oneapi/tbb/concurrent_hash_map.h>
#pragma GCC diagnostic pop

#include <cstdint>
#include <limits>
#include <memory>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
using Delta = std::pair<T const, T>;

using AccountDelta = Delta<std::optional<Account>>;

static_assert(sizeof(AccountDelta) == 176);
static_assert(alignof(AccountDelta) == 8);

/// Sentinel for `last_mutated`: the key has not been mutated by any
/// transaction within the current block. Read-only keys, and keys written
/// only by the block prologue/epilogue (which merge with no owning
/// transaction index), keep this value.
inline constexpr uint64_t LAST_MUTATED_NONE =
    std::numeric_limits<uint64_t>::max();

/// A single storage slot's within-block delta. `first` is the pre-block value
/// (read from `monadb` on first access) and `second` is the current
/// within-block value (updated as transactions merge). `last_mutated` is the
/// block-relative index of the last transaction that wrote `second`, or
/// `LAST_MUTATED_NONE` if no in-block transaction has written this slot. It is
/// purely an in-memory parallelism signal and is never flushed to `monadb`.
struct StorageDelta
{
    bytes32_t const first;
    bytes32_t second;
    uint64_t last_mutated{LAST_MUTATED_NONE};
};

static_assert(sizeof(StorageDelta) == 72);
static_assert(alignof(StorageDelta) == 8);

using StorageDeltas = oneapi::tbb::concurrent_hash_map<
    bytes32_t, StorageDelta, BytesHashCompare<bytes32_t>>;

static_assert(sizeof(StorageDeltas) == 576);
static_assert(alignof(StorageDeltas) == 8);

struct StateDelta
{
    AccountDelta account;
    StorageDeltas storage{};
    /// Block-relative index of the last transaction that mutated the account
    /// portion (balance/nonce/code/existence), or `LAST_MUTATED_NONE`. See
    /// `StorageDelta::last_mutated`.
    uint64_t account_last_mutated{LAST_MUTATED_NONE};
};

static_assert(sizeof(StateDelta) == 760);
static_assert(alignof(StateDelta) == 8);

using StateDeltas = oneapi::tbb::concurrent_hash_map<
    Address, StateDelta, BytesHashCompare<Address>>;

static_assert(sizeof(StateDeltas) == 576);
static_assert(alignof(StateDeltas) == 8);

using Code = oneapi::tbb::concurrent_hash_map<
    bytes32_t, vm::SharedIntercode, BytesHashCompare<bytes32_t>>;

static_assert(sizeof(Code) == 576);
static_assert(alignof(Code) == 8);

MONAD_NAMESPACE_END
