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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/vm.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#include <oneapi/tbb/concurrent_hash_map.h>
#pragma GCC diagnostic pop

#include <memory>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

template <class T>
using Delta = std::pair<T const, T>;

using AccountDelta = Delta<std::optional<Account>>;

static_assert(sizeof(AccountDelta) == 176);
static_assert(alignof(AccountDelta) == 8);

using PageStorageDelta = Delta<bytes4k_t>;

static_assert(sizeof(PageStorageDelta) == 8192);
static_assert(alignof(PageStorageDelta) == 1);

using PageStorageDeltas = oneapi::tbb::concurrent_hash_map<
    bytes32_t, PageStorageDelta, BytesHashCompare<bytes32_t>>;

static_assert(sizeof(PageStorageDeltas) == 576);
static_assert(alignof(PageStorageDeltas) == 8);

// Maps page_key -> list of original slot keys for that page
using PageSlotKeys = oneapi::tbb::concurrent_hash_map<
    bytes32_t, std::vector<bytes32_t>, BytesHashCompare<bytes32_t>>;

struct StateDelta
{
    AccountDelta account;
    PageStorageDeltas storage{};
    PageSlotKeys slot_keys{};
};

static_assert(sizeof(StateDelta) == 1328);
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
