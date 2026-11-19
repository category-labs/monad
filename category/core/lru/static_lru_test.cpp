// Copyright (C) 2025 Category Labs, Inc.
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
#include <category/core/lru/static_lru_cache.hpp>

#include <gtest/gtest.h>

#include <memory>
#include <string>

TEST(static_lru_test, evict)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(3);
    LruCache::ConstAccessor acc;

    lru.insert(1, 0x123);
    lru.insert(2, 0xdead);
    lru.insert(3, 0xbeef);
    EXPECT_EQ(lru.size(), 3);

    ASSERT_TRUE(lru.find(acc, 3));
    EXPECT_EQ(acc->second->val, 0xbeef);
    ASSERT_TRUE(lru.find(acc, 2));
    EXPECT_EQ(acc->second->val, 0xdead);
    ASSERT_TRUE(lru.find(acc, 1));
    EXPECT_EQ(acc->second->val, 0x123);

    lru.insert(4, 0xcafe);
    EXPECT_EQ(lru.size(), 3);

    ASSERT_TRUE(lru.find(acc, 2));
    EXPECT_EQ(acc->second->val, 0xdead);
    ASSERT_TRUE(lru.find(acc, 1));
    EXPECT_EQ(acc->second->val, 0x123);
    ASSERT_TRUE(lru.find(acc, 4));
    EXPECT_EQ(acc->second->val, 0xcafe);

    lru.insert(2, 0xc0ffee);
    lru.insert(5, 100);
    EXPECT_EQ(lru.size(), 3);

    ASSERT_TRUE(lru.find(acc, 2));
    EXPECT_EQ(acc->second->val, 0xc0ffee);
    ASSERT_TRUE(lru.find(acc, 4));
    EXPECT_EQ(acc->second->val, 0xcafe);
    ASSERT_TRUE(lru.find(acc, 5));
    EXPECT_EQ(acc->second->val, 100);
}

TEST(static_lru_test, repeated_access)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(3);
    LruCache::ConstAccessor acc;

    lru.insert(1, 100);
    lru.insert(2, 200);
    lru.insert(3, 300);

    ASSERT_TRUE(lru.find(acc, 1));
    ASSERT_TRUE(lru.find(acc, 1));
    ASSERT_TRUE(lru.find(acc, 1));
    ASSERT_TRUE(lru.find(acc, 3));
    ASSERT_TRUE(lru.find(acc, 3));
    ASSERT_TRUE(lru.find(acc, 3));

    lru.insert(4, 400);

    EXPECT_FALSE(lru.find(acc, 2));
    ASSERT_TRUE(lru.find(acc, 1));
    EXPECT_EQ(acc->second->val, 100);
    ASSERT_TRUE(lru.find(acc, 3));
    EXPECT_EQ(acc->second->val, 300);
    ASSERT_TRUE(lru.find(acc, 4));
    EXPECT_EQ(acc->second->val, 400);
}

TEST(static_lru_test, insert_return)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(3);
    {
        auto const [map_it, erased_value] = lru.insert(1, 100);
        ASSERT_FALSE(erased_value.has_value());
        EXPECT_EQ(map_it->second->key, 1);
        EXPECT_EQ(map_it->second->val, 100);
    }
    {
        auto const [map_it, erased_value] = lru.insert(2, 200);
        ASSERT_FALSE(erased_value.has_value());
        EXPECT_EQ(map_it->second->key, 2);
        EXPECT_EQ(map_it->second->val, 200);
    }
    {
        auto const [map_it, erased_value] = lru.insert(3, 300);
        ASSERT_FALSE(erased_value.has_value());
        EXPECT_EQ(map_it->second->key, 3);
        EXPECT_EQ(map_it->second->val, 300);
    }
    {
        auto const [map_it, erased_value] = lru.insert(4, 400);
        ASSERT_TRUE(erased_value.has_value());
        EXPECT_EQ(*erased_value, 100);
        EXPECT_EQ(map_it->second->key, 4);
        EXPECT_EQ(map_it->second->val, 400);
    }
}

TEST(static_lru_test, clear)
{
    using LruCache = monad::static_lru_cache<int, std::string>;
    LruCache lru(3);
    LruCache::ConstAccessor acc;

    lru.insert(1, "hello");
    lru.insert(2, "world");

    ASSERT_TRUE(lru.find(acc, 1));
    EXPECT_EQ(acc->second->val, "hello");
    ASSERT_TRUE(lru.find(acc, 2));
    EXPECT_EQ(acc->second->val, "world");
    EXPECT_EQ(lru.size(), 2);

    lru.clear();
    EXPECT_EQ(lru.size(), 0);
    EXPECT_FALSE(lru.find(acc, 1));
    EXPECT_FALSE(lru.find(acc, 2));

    lru.insert(5, "world");
    EXPECT_EQ(lru.size(), 1);
}

TEST(static_lru_test, counts_hits_misses_and_evictions)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(2);
    LruCache::ConstAccessor acc;

    EXPECT_FALSE(lru.find(acc, 1));
    lru.insert(1, 0x111);
    lru.insert(2, 0x222);
    ASSERT_TRUE(lru.find(acc, 1));
    EXPECT_EQ(lru.stats().evictions, 0u);

    lru.insert(3, 0x333);

    auto const stats = lru.stats();
    EXPECT_EQ(stats.hits, 1u);
    EXPECT_EQ(stats.misses, 1u);
    EXPECT_EQ(stats.evictions, 1u);
}

// An existence check must not move the hit rate, and must not count as a use
// that keeps the entry alive.
TEST(static_lru_test, contains_neither_counts_nor_reorders)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(2);

    lru.insert(1, 0x111);
    lru.insert(2, 0x222);

    EXPECT_TRUE(lru.contains(1));
    EXPECT_FALSE(lru.contains(3));

    auto const stats = lru.stats();
    EXPECT_EQ(stats.hits, 0u);
    EXPECT_EQ(stats.misses, 0u);

    // 1 is still the LRU tail, so it is what the next insert displaces.
    lru.insert(3, 0x333);
    EXPECT_FALSE(lru.contains(1));
    EXPECT_TRUE(lru.contains(2));
}

// The recycled nodes drop their values, or a cache of shared_ptr keeps
// everything it ever held alive.
TEST(static_lru_test, clear_releases_the_stored_values)
{
    using LruCache = monad::static_lru_cache<int, std::shared_ptr<int>>;
    LruCache lru(2);

    auto const held = std::make_shared<int>(7);
    lru.insert(1, held);
    ASSERT_EQ(held.use_count(), 2);

    lru.clear();

    EXPECT_EQ(held.use_count(), 1);
}

TEST(static_lru_test, clear_does_not_leave_a_phantom_eviction)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(2);

    lru.insert(1, 0x111);
    lru.insert(2, 0x222);
    ASSERT_EQ(lru.stats().evictions, 0u);

    lru.clear();
    ASSERT_EQ(lru.size(), 0);

    // The cache is empty, so this insert needs no room and must not report
    // evicting the entry clear() already removed.
    lru.insert(3, 0x333);

    EXPECT_EQ(lru.size(), 1);
    EXPECT_EQ(lru.stats().evictions, 0u);
}

TEST(static_lru_test, overwriting_an_existing_key_does_not_evict)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(2);

    lru.insert(1, 0x111);
    lru.insert(1, 0x222);

    EXPECT_EQ(lru.size(), 1);
    EXPECT_EQ(lru.stats().evictions, 0u);
}

// The reason the block is refcounted rather than a member: a scraper holding a
// handle keeps reading after the cache it came from is destroyed, so a cache
// owned by a worker thread's stack frame can still be observed. The counters
// are lifetime totals and survive; occupancy is a level, and a cache that no
// longer exists holds nothing.
TEST(static_lru_test, stats_handle_outlives_the_cache)
{
    using LruCache = monad::static_lru_cache<int, int>;

    std::shared_ptr<monad::CacheStats const> handle;
    {
        LruCache lru(2);
        LruCache::ConstAccessor acc;
        lru.insert(1, 0x111);
        ASSERT_TRUE(lru.find(acc, 1));
        EXPECT_FALSE(lru.find(acc, 2));
        handle = lru.stats_handle();

        auto const live = handle->snapshot();
        ASSERT_EQ(live.entries, 1u);
        ASSERT_EQ(live.max_entries, 2u);
    }

    auto const s = handle->snapshot();
    EXPECT_EQ(s.hits, 1u);
    EXPECT_EQ(s.misses, 1u);
    // Not 1: reporting the last live reading forever would show a phantom
    // cache holding entries.
    EXPECT_EQ(s.entries, 0u);
    EXPECT_EQ(s.used_bytes, 0u);
}

namespace
{
    class deferring_cache : public monad::static_lru_cache<int, int>
    {
        using Base = monad::static_lru_cache<int, int>;

    public:
        using Base::Base;
        using Base::defer_occupancy;
        using Base::evict_lru_tail;
    };
}

// A derived cache with a byte bound of its own defers occupancy so both
// levels land in one publish, which leaves the published count behind the map
// until it does. size() reads the map through that window because it is what
// such a cache's eviction loop guards on, and a loop guarding on a count that
// cannot fall keeps evicting once the last entry is already gone.
TEST(static_lru_test, size_reads_the_map_while_occupancy_is_deferred)
{
    deferring_cache lru(3);
    lru.insert(1, 0x111);
    lru.insert(2, 0x222);
    lru.insert(3, 0x333);
    ASSERT_EQ(lru.size(), 3u);

    lru.defer_occupancy();
    lru.evict_lru_tail();
    lru.evict_lru_tail();

    EXPECT_EQ(lru.size(), 1u);
    // Behind by design: the derived cache publishes both levels together once
    // it knows its byte total.
    EXPECT_EQ(lru.stats().entries, 3u);
}
