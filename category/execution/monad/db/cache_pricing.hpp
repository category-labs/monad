// Copyright (C) 2026 Category Labs, Inc.
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

// Fixed-window state caching: every live account / storage page carries a
// consensus stamp (block number of its last selected access) on its DbCache
// entry. An item is cached at block N iff it was stamped within the last
// CACHE_WINDOW_BLOCKS blocks; the first access to a cached item in a
// transaction charges the cached tier instead of cold. Each block stamps at
// most a capped number of items (selection in commit_builder.cpp), so the
// cached set is bounded, and writes its selected keys into the stamp log
// (stamp_log.hpp) as ordinary state of STAMP_LOG_ADDRESS.

#include <category/core/address.hpp>
#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

inline constexpr uint64_t CACHE_WINDOW_BLOCKS = 1000;
inline constexpr uint64_t CACHE_REFRESH_PERIOD_BLOCKS = CACHE_WINDOW_BLOCKS / 2;
inline constexpr uint64_t MAX_ACCOUNT_STAMPS_PER_BLOCK = 5000;
// sum of occupied slots over the pages stamped in a block
inline constexpr uint64_t MAX_STORAGE_SLOT_STAMPS_PER_BLOCK = 5000;

// Placeholder for the reserved system account holding the stamp log; the
// final value is a protocol decision. Unreachable from the EVM: excluded from
// stamping and pricing, its storage is written only by the commit path.
inline constexpr Address STAMP_LOG_ADDRESS =
    address_from_hex("0x0000000000000000000000000000000000c4c4e0");

// Cached at block N: stamped within the window. Stamp 0 means unstamped.
inline bool cache_stamp_cached(uint64_t const stamp, uint64_t const block)
{
    return stamp != 0 && stamp + CACHE_WINDOW_BLOCKS >= block;
}

// Stale at block N: a cached read re-stamps only when the stamp is older
// than the refresh period.
inline bool cache_stamp_stale(uint64_t const stamp, uint64_t const block)
{
    return stamp + CACHE_REFRESH_PERIOD_BLOCKS < block;
}

// Physical eviction floor once block `finalized` is finalized: every entry
// stamped at or above it may still price cached and must stay resident.
inline uint64_t cache_evict_floor(uint64_t const finalized)
{
    return finalized > CACHE_WINDOW_BLOCKS ? finalized - CACHE_WINDOW_BLOCKS
                                           : 0;
}

MONAD_NAMESPACE_END
