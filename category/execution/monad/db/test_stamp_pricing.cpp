// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/core/address.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/stamp_blob.hpp>

#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <optional>

using namespace monad;

TEST(StampWindow, boundary_advances_with_capacity)
{
    StampWindow w{10};
    // blocks 1..5, weight 3 each: 15 total > 10
    for (uint64_t b = 1; b <= 5; ++b) {
        w.apply(0, b, 0, 3);
    }
    EXPECT_EQ(w.boundary(), 0);
    w.advance();
    // pops blocks 1 and 2 (15 -> 12 -> 9)
    EXPECT_EQ(w.boundary(), 3);
    EXPECT_EQ(w.total(), 9);
    // E is monotone: removing weight does not move it back
    w.apply(4, 0, 3, 0);
    w.advance();
    EXPECT_EQ(w.boundary(), 3);
}

TEST(StampWindow, restamp_moves_weight)
{
    StampWindow w{100};
    w.apply(0, 1, 0, 5);
    w.apply(1, 9, 5, 5);
    w.advance();
    EXPECT_EQ(w.total(), 5);
    EXPECT_EQ(w.boundary(), 0);
}

TEST(StampWindow, decrement_below_boundary_is_noop)
{
    StampWindow w{4};
    w.apply(0, 1, 0, 3);
    w.apply(0, 2, 0, 3);
    w.advance(); // pops block 1
    EXPECT_EQ(w.boundary(), 2);
    uint64_t const total = w.total();
    // a re-stamp whose prev bucket was already popped must not double-count
    w.apply(1, 3, 3, 3);
    EXPECT_EQ(w.total(), total + 3);
}

TEST(StampRefresh, rule)
{
    // depth = N - E = 1000, threshold = max(500, 64) = 500
    EXPECT_TRUE(cache_stamp_refresh_due(400, 2000, 1000));
    EXPECT_FALSE(cache_stamp_refresh_due(1600, 2000, 1000));
    // shallow window: floor dominates
    EXPECT_TRUE(cache_stamp_refresh_due(100, 2000, 1990));
    EXPECT_FALSE(cache_stamp_refresh_due(1990, 2000, 1990));
    // young chain: nothing older than the floor exists
    EXPECT_FALSE(cache_stamp_refresh_due(1, 50, 0));
}

TEST(StampLru, stamp_order_eviction_and_negative_list)
{
    LruCache<int, std::optional<int>> cache{
        /*max_size=*/3, /*stamp_mode=*/true, /*negative_max=*/2};
    cache.set_evict_floor(0);

    // negatives never displace live entries
    for (int k = 0; k < 3; ++k) {
        cache.insert(k, k);
        cache.set_stamp(k, static_cast<uint64_t>(k) + 1);
    }
    for (int k = 100; k < 110; ++k) {
        cache.insert(k, std::nullopt, /*negative=*/true);
    }
    for (int k = 0; k < 3; ++k) {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, k));
        EXPECT_EQ(cache.stamp_of(acc), static_cast<uint64_t>(k) + 1);
    }

    // window advanced past stamp 1: key 0 is cold and evictable; a fourth
    // live insert evicts exactly it (a warm victim would abort)
    cache.set_evict_floor(2);
    cache.insert(50, 50);
    {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        EXPECT_FALSE(cache.find(acc, 0));
        ASSERT_TRUE(cache.find(acc, 50));
        EXPECT_EQ(cache.stamp_of(acc), 0); // unstamped until finalize
    }

    // deletion flips the entry to the negative list in place
    cache.insert(1, std::nullopt, /*negative=*/true);
    {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, 1));
        EXPECT_TRUE(cache.is_negative(acc));
        EXPECT_EQ(cache.stamp_of(acc), 0);
    }
    // and creation flips it back, unstamped
    cache.insert(1, 11);
    {
        LruCache<int, std::optional<int>>::ConstAccessor acc;
        ASSERT_TRUE(cache.find(acc, 1));
        EXPECT_FALSE(cache.is_negative(acc));
        EXPECT_EQ(cache.stamp_of(acc), 0);
    }
}

TEST(StampBlobIo, round_trip_and_corruption)
{
    auto const dir =
        std::filesystem::temp_directory_path() / "mbc_stamp_blob_test";
    std::filesystem::remove_all(dir);

    StampBlob in;
    in.block = 42;
    in.account_stamps.push_back(
        {.address = Address{0x1},
         .prev_stamp = 7,
         .prev_weight = 1,
         .weight = 1});
    in.storage_stamps.push_back(
        {.key = StorageKey{Address{0x2}, Incarnation{3, 4}, bytes32_t{0x5}},
         .prev_stamp = 9,
         .prev_weight = 40,
         .weight = 0});
    write_stamp_blob(dir, in.block, in.account_stamps, in.storage_stamps);

    ASSERT_EQ(list_stamp_blobs(dir), std::vector<uint64_t>{42});
    auto const out = read_stamp_blob(dir / "42.blob");
    ASSERT_TRUE(out.has_value());
    EXPECT_EQ(out->block, 42);
    ASSERT_EQ(out->account_stamps.size(), 1u);
    EXPECT_EQ(out->account_stamps[0].address, Address{0x1});
    EXPECT_EQ(out->account_stamps[0].prev_stamp, 7);
    ASSERT_EQ(out->storage_stamps.size(), 1u);
    EXPECT_EQ(out->storage_stamps[0].key, in.storage_stamps[0].key);
    EXPECT_EQ(out->storage_stamps[0].prev_stamp, 9);
    EXPECT_EQ(out->storage_stamps[0].prev_weight, 40u);
    EXPECT_EQ(out->storage_stamps[0].weight, 0u);

    // flip one payload byte: the hash check must reject the blob
    {
        std::fstream f(
            dir / "42.blob", std::ios::binary | std::ios::in | std::ios::out);
        f.seekp(20);
        char c;
        f.seekg(20);
        f.get(c);
        f.seekp(20);
        f.put(static_cast<char>(c ^ 1));
    }
    EXPECT_FALSE(read_stamp_blob(dir / "42.blob").has_value());
    std::filesystem::remove_all(dir);
}
