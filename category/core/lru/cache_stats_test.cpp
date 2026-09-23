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

// Snapshots are cumulative, not draining: two readers must not steal counts
// from each other.
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

TEST(cache_stats_test, occupancy_is_a_level_not_a_total)
{
    CacheStats stats;
    stats.publish_occupancy(400, 4);
    ASSERT_EQ(stats.snapshot().used_bytes, 400u);

    stats.publish_occupancy(100, 1);

    auto const s = stats.snapshot();
    EXPECT_EQ(s.used_bytes, 100u);
    EXPECT_EQ(s.entries, 1u);
}

// A reader holding only a snapshot has no other way to turn the two levels
// into a utilisation figure.
TEST(cache_stats_test, snapshot_carries_its_own_bounds)
{
    CacheStats stats;
    stats.publish_capacity(4096, 39);
    stats.publish_occupancy(2048, 20);

    auto const s = stats.snapshot();
    EXPECT_EQ(s.max_bytes, 4096u);
    EXPECT_EQ(s.max_entries, 39u);
    EXPECT_EQ(s.used_bytes, 2048u);
    EXPECT_EQ(s.entries, 20u);
}

// The block is shared with readers, so it must not be copyable out from under
// them or movable away from the cache that writes it.
static_assert(!std::is_copy_constructible_v<CacheStats>);
static_assert(!std::is_move_constructible_v<CacheStats>);
