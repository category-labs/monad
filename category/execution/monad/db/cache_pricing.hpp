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

// Multi-block cache pricing: consensus parameters, the per-blocknum weight
// histogram stored under CACHE_PRICING_NIBBLE, and the capacity cutoff.
//
// The histogram maps block number -> total weight of live entries whose
// stored last_access equals that block (accounts weigh 1, storage pages weigh
// their occupied-slot count). The cutoff B* for block N is the newest block
// where the weight of blocks (B*, N) exceeds the capacity; an entry is priced
// "cached" iff its last_access > B* (the boundary block is excluded).

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct Db;

// C: a last_access is only rewritten when at least this many blocks old,
// bounding trie churn to one leaf rewrite per entry per C blocks. The stored
// value therefore lags the true last access by up to C - 1 blocks.
inline constexpr uint64_t CACHE_PRICING_UPDATE_INTERVAL = 256;

// Modeled pricing-cache capacities; sized below the physical DbCache so the
// priced-cached window is actually resident.
inline constexpr uint64_t CACHE_PRICING_ACCOUNT_CAPACITY = 5'000'000;
inline constexpr uint64_t CACHE_PRICING_STORAGE_SLOT_CAPACITY = 5'000'000;

// W: histogram window; buckets older than N - W are dead (pruned) and any
// entry with last_access <= N - W is unconditionally cold.
inline constexpr uint64_t CACHE_PRICING_WINDOW = 1'000'000;

// bucket key holding the oldest live bucket block, bounding the cutoff walk;
// real buckets are keyed by last_access, which is never zero
inline constexpr uint64_t CACHE_PRICING_META_BUCKET = 0;

enum class PricingKind : uint8_t
{
    account = 0,
    storage = 1,
};

constexpr bool
cache_pricing_bump_due(uint64_t const last_access, uint64_t const block)
{
    // 0 = never accessed, always due
    return last_access == 0 ||
           block - last_access >= CACHE_PRICING_UPDATE_INTERVAL;
}

// Histogram leaf key under CACHE_PRICING_NIBBLE: kind byte + block big endian.
byte_string cache_pricing_bucket_key(PricingKind, uint64_t block);

struct PricingCutoffs
{
    // cached iff last_access > cutoff
    uint64_t account;
    uint64_t storage;
};

// Walks histogram buckets of the db's current (parent) prefix newest to
// oldest, accumulating weight until each capacity is exceeded.
PricingCutoffs compute_pricing_cutoffs(Db &, uint64_t block);

MONAD_NAMESPACE_END
