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

// Measurement counters of the cached tier, collected per transaction and
// merged into the block for committed transactions only (a retried
// execution counts once).
struct CacheTierStats
{
    // inter-touch gap (block - stamp) buckets of stamped items at their
    // first access: <=100, <=250, <=500, <=1000, <=2000, >2000
    static constexpr uint64_t GAP_BOUNDS[] = {100, 250, 500, 1000, 2000};
    static constexpr size_t GAP_BUCKETS = 6;

    uint64_t cached_accounts{0}; // first accesses priced cached
    uint64_t cached_storage{0};
    uint64_t first_accounts{0}; // first accesses of the transaction
    uint64_t missing_accounts{0}; // of which the item had no trie leaf
    uint64_t first_storage{0};
    uint64_t missing_storage{0};
    uint64_t account_gaps[GAP_BUCKETS]{};
    uint64_t storage_gaps[GAP_BUCKETS]{};

    static void record_gap(uint64_t (&buckets)[GAP_BUCKETS], uint64_t const gap)
    {
        size_t i = 0;
        while (i < GAP_BUCKETS - 1 && gap > GAP_BOUNDS[i]) {
            ++i;
        }
        ++buckets[i];
    }

    void add(CacheTierStats const &o)
    {
        cached_accounts += o.cached_accounts;
        cached_storage += o.cached_storage;
        first_accounts += o.first_accounts;
        missing_accounts += o.missing_accounts;
        first_storage += o.first_storage;
        missing_storage += o.missing_storage;
        for (size_t i = 0; i < GAP_BUCKETS; ++i) {
            account_gaps[i] += o.account_gaps[i];
            storage_gaps[i] += o.storage_gaps[i];
        }
    }
};

MONAD_NAMESPACE_END
