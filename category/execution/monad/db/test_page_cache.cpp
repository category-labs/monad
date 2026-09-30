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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/page_cache.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

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

namespace
{
    std::vector<StorageKey> make_records(size_t const n)
    {
        std::vector<StorageKey> records;
        for (size_t i = 0; i < n; ++i) {
            records.emplace_back(
                Address{0x1000 + i}, Incarnation{0, 0}, bytes32_t{i * 7 + 1});
        }
        return records;
    }

    // Byte i of the page, slot k holding bytes 32k .. 32k + 31.
    uint8_t byte_at(storage_page_t const &page, size_t const i)
    {
        return page[static_cast<uint8_t>(i / 32)].bytes[i % 32];
    }
}

TEST(PageCache, log_page_layout)
{
    auto const records = make_records(3);
    storage_page_t const page = encode_log_page(0xaabb, 0xccdd, records);
    EXPECT_EQ(byte_at(page, 6), 0xaa);
    EXPECT_EQ(byte_at(page, 7), 0xbb);
    EXPECT_EQ(byte_at(page, 14), 0xcc);
    EXPECT_EQ(byte_at(page, 15), 0xdd);
    EXPECT_EQ(byte_at(page, 16), 0);
    EXPECT_EQ(byte_at(page, 17), 3);
    for (size_t k = 0; k < 3; ++k) {
        size_t const rec = 24 + 52 * k;
        for (size_t i = 0; i < 20; ++i) {
            EXPECT_EQ(byte_at(page, rec + i), records[k].bytes[i]);
        }
        for (size_t i = 0; i < 32; ++i) {
            EXPECT_EQ(byte_at(page, rec + 20 + i), records[k].bytes[28 + i]);
        }
    }
    // Header and three records fill 180 bytes, so slots 6 and up are zero.
    for (uint8_t off = 6; off < storage_page_t::SLOTS; ++off) {
        EXPECT_EQ(page[off], bytes32_t{}) << int{off};
    }
}

TEST(PageCache, log_page_round_trip)
{
    for (size_t const n : {size_t{1}, size_t{2}, size_t{77}, size_t{78}}) {
        auto const records = make_records(n);
        auto const decoded =
            decode_log_page(encode_log_page(42, 1234, records), 1234);
        ASSERT_TRUE(decoded.has_value()) << n;
        EXPECT_EQ(
            decoded.value(),
            (PageCacheLogPage{
                .block_number = 42, .stamp = 1234, .records = records}));
    }
    // A full page uses 4,080 bytes, so the last 16 bytes of slot 127 are
    // zero.
    storage_page_t const full = encode_log_page(1, 0, make_records(78));
    EXPECT_NE(byte_at(full, 4079), 0);
    for (size_t i = 4080; i < 4096; ++i) {
        EXPECT_EQ(byte_at(full, i), 0) << i;
    }
}

TEST(PageCache, log_page_rejects)
{
    storage_page_t const page = encode_log_page(5, 10, make_records(4));
    auto const wrong_stamp = decode_log_page(page, 11);
    ASSERT_TRUE(wrong_stamp.has_error());
    EXPECT_EQ(wrong_stamp.error(), PageCacheError::WrongStamp);

    // A never-written ring index is an empty page: stamp 0 with no records.
    auto const empty = decode_log_page(storage_page_t{}, 0);
    ASSERT_TRUE(empty.has_error());
    EXPECT_EQ(empty.error(), PageCacheError::BadRecordCount);

    storage_page_t too_many = page;
    bytes32_t word = too_many[0];
    word.bytes[17] = 79;
    too_many.set(0, word);
    auto const bad_count = decode_log_page(too_many, 10);
    ASSERT_TRUE(bad_count.has_error());
    EXPECT_EQ(bad_count.error(), PageCacheError::BadRecordCount);

    EXPECT_DEATH(encode_log_page(5, 10, {}), "records");
    EXPECT_DEATH(encode_log_page(5, 10, make_records(79)), "records");
    std::vector<StorageKey> const with_incarnation{
        StorageKey{Address{1}, Incarnation{3, 0}, bytes32_t{uint64_t{1}}}};
    EXPECT_DEATH(encode_log_page(5, 10, with_incarnation), "incarnation");
}
