#include <category/core/lru/static_lru_cache.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

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
