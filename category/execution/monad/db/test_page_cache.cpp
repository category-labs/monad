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

#include <category/core/bytes.hpp>
#include <category/execution/monad/db/page_cache.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;

TEST(PageCache, parameter_relations)
{
    // Capacity eviction pops whole log pages and may over-evict by up to
    // 78 x 128 = 9,984 slot units, under 0.1 block of admissions, so a page
    // still stays cached for about MIN_LIVENESS blocks.
    static_assert(
        PAGE_CACHE_CAPACITY / PAGE_CACHE_MAX_ADMISSION_PER_BLOCK ==
        PAGE_CACHE_MIN_LIVENESS);
    static_assert(
        PAGE_CACHE_RING_BUFFER_SIZE / PAGE_CACHE_MAX_LOG_PAGES_PER_BLOCK ==
        PAGE_CACHE_MIN_LIVENESS);
    // The derivation of q from the 150M block gas limit.
    static_assert(
        150'000'000 / PAGE_CACHE_MAX_ADMISSION_PER_BLOCK ==
        PAGE_CACHE_ADMISSION_GAS_PER_SLOT);
    // h >= q: growth gas covers the admission requirement of a grown slot.
    static_assert(
        MonadTraits<MONAD_NEXT>::page_growth_cost() >=
        static_cast<int64_t>(PAGE_CACHE_ADMISSION_GAS_PER_SLOT));
}

TEST(PageCache, page_keys)
{
    EXPECT_EQ(PAGE_CACHE_CURSOR_PAGE_KEY, bytes32_t{});
    EXPECT_EQ(page_cache_log_page_key(0), bytes32_t{uint64_t{1}});
    EXPECT_EQ(
        page_cache_log_page_key(PAGE_CACHE_RING_BUFFER_SIZE - 1),
        bytes32_t{PAGE_CACHE_RING_BUFFER_SIZE});
    // Slot k of the log page at ring index 0 is slot key 128 + k.
    EXPECT_EQ(
        compute_slot_key(page_cache_log_page_key(0), uint8_t{5}),
        bytes32_t{uint64_t{128 + 5}});
    EXPECT_DEATH(
        page_cache_log_page_key(PAGE_CACHE_RING_BUFFER_SIZE), "ring_index");
}

TEST(PageCache, cursor)
{
    PageCacheCursor const cursor{
        .head = 0x0102030405060708, .tail = 0x1112131415161718};
    storage_page_t const page = encode_cursor(cursor);
    EXPECT_EQ(page.size(), 1);
    bytes32_t const word = page[0];
    EXPECT_EQ(word.bytes[0], 0x01);
    EXPECT_EQ(word.bytes[7], 0x08);
    EXPECT_EQ(word.bytes[8], 0x11);
    EXPECT_EQ(word.bytes[15], 0x18);
    for (size_t i = 16; i < sizeof(word.bytes); ++i) {
        EXPECT_EQ(word.bytes[i], 0) << i;
    }
    EXPECT_EQ(decode_cursor(page).value(), cursor);

    // A never-written cursor page is an empty page: head = tail = 0.
    EXPECT_TRUE(encode_cursor({}).is_empty());
    EXPECT_EQ(decode_cursor(storage_page_t{}).value(), PageCacheCursor{});

    bytes32_t bad{};
    bad.bytes[7] = 2; // head = 2, tail = 0
    auto const res = decode_cursor(storage_page_t{bad});
    ASSERT_TRUE(res.has_error());
    EXPECT_EQ(res.error(), PageCacheError::CursorOutOfOrder);
}
