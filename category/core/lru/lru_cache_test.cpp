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
#include <category/core/lru/lru_cache.hpp>

#include <gtest/gtest.h>

using Cache = monad::LruCache<int, int>;

TEST(lru_cache_test, find_counts_hit_and_miss)
{
    Cache cache{4};
    Cache::ConstAccessor acc;

    EXPECT_FALSE(cache.find(acc, 1));
    cache.insert(1, 0x111);
    ASSERT_TRUE(cache.find(acc, 1));

    auto const stats = cache.stats();
    EXPECT_EQ(stats.hits, 1u);
    EXPECT_EQ(stats.misses, 1u);
}

TEST(lru_cache_test, stats_are_not_reset_by_reading_them)
{
    Cache cache{4};
    Cache::ConstAccessor acc;

    cache.insert(1, 0x111);
    ASSERT_TRUE(cache.find(acc, 1));

    auto const first = cache.stats();
    auto const second = cache.stats();
    EXPECT_EQ(first.hits, 1u);
    EXPECT_EQ(second.hits, first.hits);
    EXPECT_EQ(second.misses, first.misses);
    EXPECT_EQ(second.evictions, first.evictions);
}

TEST(lru_cache_test, counts_evictions_once_capacity_is_exceeded)
{
    Cache cache{2};

    cache.insert(1, 0x111);
    cache.insert(2, 0x222);
    EXPECT_EQ(cache.stats().evictions, 0u);

    cache.insert(3, 0x333);
    EXPECT_EQ(cache.size(), 2u);
    EXPECT_EQ(cache.stats().evictions, 1u);
}

TEST(lru_cache_test, overwriting_an_existing_key_does_not_evict)
{
    Cache cache{2};

    cache.insert(1, 0x111);
    cache.insert(1, 0x222);

    EXPECT_EQ(cache.size(), 1u);
    EXPECT_EQ(cache.stats().evictions, 0u);
}

TEST(cache_stats_window_test, reports_activity_since_the_last_reset)
{
    Cache cache{4};
    Cache::ConstAccessor acc;
    monad::CacheStatsWindow window;

    cache.insert(1, 0x111);
    ASSERT_TRUE(cache.find(acc, 1));
    window.reset(cache.stats());

    ASSERT_TRUE(cache.find(acc, 1));
    EXPECT_FALSE(cache.find(acc, 2));

    EXPECT_EQ(cache.stats().hits, 2u);
    EXPECT_EQ(cache.stats().misses, 1u);

    auto const since = window.since(cache.stats());
    EXPECT_EQ(since.hits, 1u);
    EXPECT_EQ(since.misses, 1u);
}

// A counter can only go backwards if a window is used against the wrong cache.
// Saturating keeps that bug legible as "no activity" instead of ~1.8e19.
TEST(cache_stats_window_test, a_backwards_counter_saturates_instead_of_wrapping)
{
    monad::CacheStatsSnapshot const earlier{
        .hits = 5, .misses = 5, .evictions = 5};
    monad::CacheStatsSnapshot const later{
        .hits = 10, .misses = 10, .evictions = 10};

    auto const forward = later - earlier;
    EXPECT_EQ(forward.hits, 5u);

    auto const backward = earlier - later;
    EXPECT_EQ(backward.hits, 0u);
    EXPECT_EQ(backward.misses, 0u);
    EXPECT_EQ(backward.evictions, 0u);
}

TEST(cache_stats_window_test, before_any_reset_the_window_is_the_whole_history)
{
    Cache cache{4};
    Cache::ConstAccessor acc;
    monad::CacheStatsWindow const window;

    cache.insert(1, 0x111);
    ASSERT_TRUE(cache.find(acc, 1));

    EXPECT_EQ(window.since(cache.stats()).hits, 1u);
}

TEST(lru_cache_test, clear_does_not_disturb_the_counters)
{
    Cache cache{4};

    // Scoped: an accessor holds a lock on its element, and clear() destroys
    // the element under it.
    {
        Cache::ConstAccessor acc;
        EXPECT_FALSE(cache.find(acc, 1));
    }
    cache.insert(1, 0x111);
    {
        Cache::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, 1));
    }

    cache.clear();

    auto const stats = cache.stats();
    EXPECT_EQ(stats.hits, 1u);
    EXPECT_EQ(stats.misses, 1u);
}
