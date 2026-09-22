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
    // A cache bounded more than one way merges its bounds here, so the total
    // does not attribute any of them.
    uint64_t evictions{0};
};

// Hit/miss/eviction counts for the life of the cache object, never reset.
//
// One writer only -- the thread that owns the cache -- so the recorders are a
// load and a store rather than a read-modify-write, which would put a locked
// instruction on the caller's hot path. Atomic so that a reader on another
// thread is not a data race; relaxed because a counter needs no ordering
// against anything else.
class CacheStats
{
    std::atomic<uint64_t> hits_{0};
    std::atomic<uint64_t> misses_{0};
    std::atomic<uint64_t> evictions_{0};

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

    [[nodiscard]] CacheStatsSnapshot snapshot() const noexcept
    {
        return {
            .hits = hits_.load(std::memory_order_relaxed),
            .misses = misses_.load(std::memory_order_relaxed),
            .evictions = evictions_.load(std::memory_order_relaxed)};
    }
};

MONAD_NAMESPACE_END
