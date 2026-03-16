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

#include <category/core/byte_string.hpp>
#include <category/core/lru/memory_bound_lru_cache.hpp>

#include <gtest/gtest.h>

#include <array>

using namespace monad;

static constexpr std::array<size_t, 4> SLAB_SIZES{32, 64, 128, 512};

using TestCache = MemoryBoundLruCache<uint64_t>;

TEST(MemoryBoundLruCache, insert_and_find)
{
    TestCache cache{4096, SLAB_SIZES};
    byte_string const value(64, 0xAB);

    cache.insert(1, value);
    EXPECT_GE(cache.used_bytes(), value.size());

    TestCache::ConstAccessor acc{};
    ASSERT_TRUE(cache.find(acc, 1));
    EXPECT_EQ(
        byte_string(acc->second.value_.begin(), acc->second.value_.end()),
        value);
}

TEST(MemoryBoundLruCache, miss_returns_false)
{
    TestCache cache{4096, SLAB_SIZES};
    TestCache::ConstAccessor acc{};
    EXPECT_FALSE(cache.find(acc, 42));
}

TEST(MemoryBoundLruCache, eviction_under_memory_pressure)
{
    TestCache cache{1024, SLAB_SIZES};
    byte_string const value(100, 0xAB);

    for (uint64_t i = 0; i < 100; ++i) {
        cache.insert(i, value);
    }

    TestCache::ConstAccessor acc{};
    EXPECT_FALSE(cache.find(acc, 0));
    EXPECT_TRUE(cache.find(acc, 99));
    EXPECT_LE(cache.used_bytes(), 1024);
}

TEST(MemoryBoundLruCache, overwrite_same_key)
{
    TestCache cache{4096, SLAB_SIZES};

    cache.insert(1, byte_string{0x01});
    cache.insert(1, byte_string{0x02});

    TestCache::ConstAccessor acc{};
    ASSERT_TRUE(cache.find(acc, 1));
    EXPECT_EQ(
        byte_string(acc->second.value_.begin(), acc->second.value_.end()),
        byte_string{0x02});
}

TEST(MemoryBoundLruCache, clear)
{
    TestCache cache{4096, SLAB_SIZES};
    cache.insert(1, byte_string{0x01});
    cache.clear();

    TestCache::ConstAccessor acc{};
    EXPECT_FALSE(cache.find(acc, 1));
    EXPECT_EQ(cache.used_bytes(), 0);
}

TEST(MemoryBoundLruCache, variable_size_entries)
{
    TestCache cache{16384, SLAB_SIZES};

    byte_string small_val{0x01, 0x02};
    cache.insert(0, small_val);

    byte_string large_val(400, 0xAB);
    cache.insert(1, large_val);

    TestCache::ConstAccessor acc0{};
    TestCache::ConstAccessor acc1{};
    ASSERT_TRUE(cache.find(acc0, 0));
    ASSERT_TRUE(cache.find(acc1, 1));
    EXPECT_EQ(
        byte_string(acc0->second.value_.begin(), acc0->second.value_.end()),
        small_val);
    EXPECT_EQ(
        byte_string(acc1->second.value_.begin(), acc1->second.value_.end()),
        large_val);
}
