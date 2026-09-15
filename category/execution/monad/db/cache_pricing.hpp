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

#include <category/core/address.hpp>
#include <category/core/config.hpp>

#include <algorithm>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

// Internal read result: a pruned proposal needs a deterministic trie-log
// lookup.
inline constexpr uint64_t CACHE_STAMP_UNKNOWN = ~uint64_t{0};

inline constexpr uint64_t CACHE_ACCOUNT_CAPACITY = 5'000'000;
inline constexpr uint64_t CACHE_STORAGE_CAPACITY = 5'000'000;
inline constexpr uint64_t CACHE_ACCOUNT_RENEWAL = 2'500'000;
inline constexpr uint64_t CACHE_STORAGE_RENEWAL = 2'500'000;
inline constexpr uint64_t CACHE_GAS_PER_CREDIT = 2000;
inline constexpr uint64_t CACHE_TX_MAX_CREDITS = 256;

inline constexpr Address STAMP_LOG_ADDRESS =
    address_from_hex("0x0000000000000000000000000000000000c4c4e0");

// All stamps are absolute record numbers, starting at 1. The parent view
// bounds valid stamps and contains the precomputed lazy-renewal boundary.
// Neither execution order nor wall-clock recency affects these boundaries.
struct CacheRingView
{
    uint64_t floor{1};
    uint64_t next{1};
    uint64_t refresh{1};
    bool operator==(CacheRingView const &) const = default;
};

struct CachePricing
{
    CacheRingView accounts;
    CacheRingView storage;
    bool operator==(CachePricing const &) const = default;
};

inline bool cache_stamp_cached(uint64_t stamp, CacheRingView const &view)
{
    return stamp >= view.floor && stamp < view.next;
}

inline bool cache_stamp_stale(uint64_t stamp, CacheRingView const &view)
{
    return stamp < view.refresh;
}

inline uint64_t cache_tx_credits(uint64_t charged_gas)
{
    return std::min(CACHE_TX_MAX_CREDITS, charged_gas / CACHE_GAS_PER_CREDIT);
}

MONAD_NAMESPACE_END
