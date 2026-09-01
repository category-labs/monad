// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <atomic>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct CacheStatsSnapshot
{
    uint64_t hits{0};
    uint64_t misses{0};
    uint64_t evictions{0}; // entries dropped to stay within the cache's bound
};

// Counters only ever increase, so a negative difference means the two
// snapshots came from different caches. Saturate rather than wrap: a window
// reading zero is a legible "no activity", where a wrap prints ~1.8e19 into
// the block metrics line and overflows the percentage back to a plausible 0%.
constexpr uint64_t
monotonic_delta(uint64_t const now, uint64_t const base) noexcept
{
    return now > base ? now - base : 0;
}

constexpr CacheStatsSnapshot
operator-(CacheStatsSnapshot const &a, CacheStatsSnapshot const &b) noexcept
{
    return {
        .hits = monotonic_delta(a.hits, b.hits),
        .misses = monotonic_delta(a.misses, b.misses),
        .evictions = monotonic_delta(a.evictions, b.evictions)};
}

// Reports cache activity over a window — a block, for the metrics log line —
// without disturbing the underlying counters, which stay cumulative. Before
// the first reset the window covers the whole history.
//
// The baseline is not atomic: reset() and since() must run on one thread, and
// both snapshots must come from the same cache.
class CacheStatsWindow
{
    CacheStatsSnapshot baseline_{};

public:
    void reset(CacheStatsSnapshot const &now) noexcept
    {
        baseline_ = now;
    }

    CacheStatsSnapshot since(CacheStatsSnapshot const &now) const noexcept
    {
        return now - baseline_;
    }
};

// Hit/miss/eviction counts for the life of the cache object. Reads are
// non-destructive, so independent readers do not consume each other's counts.
//
// The counters are relaxed because they are statistics, not synchronization —
// they order nothing and a reader tolerates a slightly stale total. The three
// loads in snapshot() are independent, so a snapshot is not a single instant;
// each counter is monotonic, which is all the window subtraction needs.
class CacheStats
{
    std::atomic<uint64_t> hits_{0};
    std::atomic<uint64_t> misses_{0};
    std::atomic<uint64_t> evictions_{0};

public:
    void record_hit() noexcept
    {
        hits_.fetch_add(1, std::memory_order_relaxed);
    }

    void record_miss() noexcept
    {
        misses_.fetch_add(1, std::memory_order_relaxed);
    }

    void record_eviction() noexcept
    {
        evictions_.fetch_add(1, std::memory_order_relaxed);
    }

    CacheStatsSnapshot snapshot() const noexcept
    {
        return {
            .hits = hits_.load(std::memory_order_relaxed),
            .misses = misses_.load(std::memory_order_relaxed),
            .evictions = evictions_.load(std::memory_order_relaxed)};
    }
};

MONAD_NAMESPACE_END
