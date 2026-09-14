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

#include <category/core/lru/cache_stats.hpp>

#include <gtest/gtest.h>

#include <type_traits>

using monad::CacheStats;
using monad::CacheStatsSnapshot;

TEST(cache_stats_test, counts_each_event_independently)
{
    CacheStats stats;
    stats.record_hit();
    stats.record_hit();
    stats.record_miss();
    stats.record_eviction();

    auto const s = stats.snapshot();
    EXPECT_EQ(s.hits, 2u);
    EXPECT_EQ(s.misses, 1u);
    EXPECT_EQ(s.evictions, 1u);
}

// The facility this replaces cleared its counters when read, so two readers
// stole counts from each other and totals could not be scraped.
TEST(cache_stats_test, reading_does_not_consume_counts)
{
    CacheStats stats;
    stats.record_hit();

    auto const first = stats.snapshot();
    auto const second = stats.snapshot();

    EXPECT_EQ(first.hits, 1u);
    EXPECT_EQ(second.hits, 1u);
}

TEST(cache_stats_test, a_fresh_snapshot_is_zeroed)
{
    CacheStatsSnapshot const s;
    EXPECT_EQ(s.hits, 0u);
    EXPECT_EQ(s.misses, 0u);
    EXPECT_EQ(s.evictions, 0u);
    EXPECT_EQ(CacheStats{}.snapshot().hits, 0u);
}

// Atomic counters make the type non-copyable, which is what keeps an embedding
// cache from being silently copied or moved along with its statistics.
static_assert(!std::is_copy_constructible_v<CacheStats>);
static_assert(!std::is_move_constructible_v<CacheStats>);
