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
    // Totals for the life of the cache; never reset.
    uint64_t hits{0};
    uint64_t misses{0};
    // A cache bounded more than one way merges its bounds here, so the total
    // does not attribute any of them.
    uint64_t evictions{0};
    // Current occupancy, not totals: these go down, and go to zero when the
    // cache is destroyed.
    uint64_t used_bytes{0};
    uint64_t entries{0};
    // The bounds the two levels above run against, so a reader holding only a
    // snapshot can compute utilisation. Zero means the cache has no such
    // bound.
    uint64_t max_bytes{0};
    uint64_t max_entries{0};
};

// The numbers a cache publishes about itself.
//
// Held by shared_ptr so a reader can outlive the cache it came from: a scraper
// on another thread keeps the block alive by holding a handle, and the cache
// can be destroyed under it without the reader touching freed memory. That
// matters for a cache owned by a worker thread's stack frame, which has no
// address a reader could be handed.
//
// One writer only -- the thread that owns the cache -- so the recorders are a
// load and a store rather than a read-modify-write, which would put a locked
// instruction on the caller's hot path. Two writers would silently lose counts
// and make a total go backwards, which a rate query reads as a counter reset.
// Atomic so that a reader on another thread is not a data race; relaxed
// because none of these orders anything else.
//
// The occupancy pair is published by one call, but as two stores, so a reader
// landing between them sees the new bytes against the old entry count. The
// window is two instructions; treat a ratio across the pair as approximate.
class CacheStats
{
    std::atomic<uint64_t> hits_{0};
    std::atomic<uint64_t> misses_{0};
    std::atomic<uint64_t> evictions_{0};
    std::atomic<uint64_t> used_bytes_{0};
    std::atomic<uint64_t> entries_{0};
    std::atomic<uint64_t> max_bytes_{0};
    std::atomic<uint64_t> max_entries_{0};

    static void bump(std::atomic<uint64_t> &counter) noexcept
    {
        counter.store(
            counter.load(std::memory_order_relaxed) + 1,
            std::memory_order_relaxed);
    }

public:
    void record_hit() noexcept
    {
        bump(hits_);
    }

    void record_miss() noexcept
    {
        bump(misses_);
    }

    void record_eviction() noexcept
    {
        bump(evictions_);
    }

    // Fixed for the life of the cache; published once when it is built.
    void publish_capacity(
        uint64_t const max_bytes, uint64_t const max_entries) noexcept
    {
        max_bytes_.store(max_bytes, std::memory_order_relaxed);
        max_entries_.store(max_entries, std::memory_order_relaxed);
    }

    // For a cache with no byte bound, where used_bytes stays zero.
    void publish_entries(uint64_t const entries) noexcept
    {
        entries_.store(entries, std::memory_order_relaxed);
    }

    void publish_occupancy(
        uint64_t const used_bytes, uint64_t const entries) noexcept
    {
        used_bytes_.store(used_bytes, std::memory_order_relaxed);
        entries_.store(entries, std::memory_order_relaxed);
    }

    [[nodiscard]] uint64_t used_bytes() const noexcept
    {
        return used_bytes_.load(std::memory_order_relaxed);
    }

    [[nodiscard]] uint64_t entries() const noexcept
    {
        return entries_.load(std::memory_order_relaxed);
    }

    [[nodiscard]] CacheStatsSnapshot snapshot() const noexcept
    {
        return {
            .hits = hits_.load(std::memory_order_relaxed),
            .misses = misses_.load(std::memory_order_relaxed),
            .evictions = evictions_.load(std::memory_order_relaxed),
            .used_bytes = used_bytes(),
            .entries = entries(),
            .max_bytes = max_bytes_.load(std::memory_order_relaxed),
            .max_entries = max_entries_.load(std::memory_order_relaxed)};
    }
};

MONAD_NAMESPACE_END
