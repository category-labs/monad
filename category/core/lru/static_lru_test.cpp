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

#include <category/core/lru/static_lru_cache.hpp>

#include <gtest/gtest.h>

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

    // Capacity is 2, so this reuses the LRU tail.
    lru.insert(3, 0x333);

    auto const stats = lru.stats();
    EXPECT_EQ(stats.hits, 1u);
    EXPECT_EQ(stats.misses, 1u);
    EXPECT_EQ(stats.evictions, 1u);
}

// find() is used as an existence predicate in a few places that are not
// lookups; those must not move the hit rate.
TEST(static_lru_test, contains_does_not_count_as_a_lookup)
{
    using LruCache = monad::static_lru_cache<int, int>;
    LruCache lru(2);

    lru.insert(1, 0x111);

    EXPECT_TRUE(lru.contains(1));
    EXPECT_FALSE(lru.contains(2));

    auto const stats = lru.stats();
    EXPECT_EQ(stats.hits, 0u);
    EXPECT_EQ(stats.misses, 0u);
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
