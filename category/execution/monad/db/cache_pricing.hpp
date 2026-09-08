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

// Multi-block cache pricing: every live account / storage entry carries a
// consensus stamp (last qualifying access block) on its DbCache entry. The
// protocol warm set is the most recent stamps that fit a per-cache budget;
// the window boundary E is counted from committed stamp records, never from
// physical cache state. Nothing is written to the trie: durability is a
// per-block sequential blob of stamp records.

#include <category/core/config.hpp>

#include <algorithm>
#include <cstdint>
#include <map>

MONAD_NAMESPACE_BEGIN

// Window budgets: accounts are counted in entries, storage in bytes of page
// weight (storage_page_t::byte_size). Both sized at half the physical cache
// of the minimum validator configuration so the warm set stays resident.
inline constexpr uint64_t ACCOUNT_WINDOW_BUDGET = 5'000'000;
inline constexpr uint64_t STORAGE_WINDOW_BUDGET = 128ull << 20;

// Lazy refresh rule: a warm read re-stamps iff the stamp is older than
// max((N - E) >> ALPHA_SHIFT, REFRESH_FLOOR) blocks.
inline constexpr unsigned CACHE_STAMP_ALPHA_SHIFT = 1;
inline constexpr uint64_t CACHE_STAMP_REFRESH_FLOOR = 64;

// Non-binding hard ceiling on stamp records per block, above the
// gas-feasible maximum; decouples client I/O provisioning from future
// gas-limit raises.
inline constexpr uint64_t K_STAMP_CEILING = 1ull << 18;

struct PricingBoundaries
{
    // warm iff stamp != 0 and stamp >= boundary
    uint64_t account;
    uint64_t storage;
};

inline bool cache_stamp_refresh_due(
    uint64_t const stamp, uint64_t const block, uint64_t const boundary)
{
    uint64_t const depth = block > boundary ? block - boundary : 0;
    uint64_t const threshold =
        std::max(depth >> CACHE_STAMP_ALPHA_SHIFT, CACHE_STAMP_REFRESH_FLOOR);
    return block > threshold && stamp < block - threshold;
}

// Per-cache window: bucket weights by stamp block, and the boundary E such
// that the weight of [E, N] fits the budget (all-or-nothing at block
// granularity). E only advances: buckets popped for capacity never return,
// and decrements below E are no-ops (those buckets are discardable).
class StampWindow
{
    std::map<uint64_t, uint64_t> counts_;
    uint64_t total_{0};
    uint64_t boundary_{0};
    uint64_t const budget_;

public:
    explicit StampWindow(uint64_t const budget)
        : budget_{budget}
    {
    }

    // prev == 0 means no previous stamp, next == 0 means the entry died.
    void apply(
        uint64_t const prev, uint64_t const next, uint64_t const prev_weight,
        uint64_t const next_weight)
    {
        if (prev >= boundary_ && prev != 0) {
            auto const it = counts_.find(prev);
            if (it != counts_.end()) {
                uint64_t const w = std::min(it->second, prev_weight);
                it->second -= w;
                total_ -= w;
                if (it->second == 0) {
                    counts_.erase(it);
                }
            }
        }
        if (next != 0) {
            counts_[next] += next_weight;
            total_ += next_weight;
        }
    }

    // Advance E for a new block: pop oldest buckets until within budget.
    void advance()
    {
        while (total_ > budget_ && !counts_.empty()) {
            auto const it = counts_.begin();
            total_ -= it->second;
            boundary_ = it->first + 1;
            counts_.erase(it);
        }
    }

    // Warm iff stamp >= boundary() and stamp != 0.
    uint64_t boundary() const
    {
        return boundary_;
    }

    uint64_t total() const
    {
        return total_;
    }
};

MONAD_NAMESPACE_END
