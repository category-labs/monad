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

// Hit/miss/eviction counts for the life of the cache object.
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

    [[nodiscard]] CacheStatsSnapshot snapshot() const noexcept
    {
        return {
            .hits = hits_.load(std::memory_order_relaxed),
            .misses = misses_.load(std::memory_order_relaxed),
            .evictions = evictions_.load(std::memory_order_relaxed)};
    }
};

MONAD_NAMESPACE_END
