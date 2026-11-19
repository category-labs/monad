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
#include <category/mpt/util.hpp>

#include <ankerl/unordered_dense.h>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad::mpt;

TEST(VirtualOffsetTest, compare)
{
    EXPECT_GT(virtual_chunk_offset_t(2, 0, 1), virtual_chunk_offset_t(2, 0, 0));
    EXPECT_GT(
        virtual_chunk_offset_t(3, 1024, 1), virtual_chunk_offset_t(3, 10, 1));
    EXPECT_GT(
        virtual_chunk_offset_t(3, 10, 1), virtual_chunk_offset_t(2, 10, 1));

    EXPECT_LT(
        virtual_chunk_offset_t(4, 50, 0), virtual_chunk_offset_t(2, 10, 1));
    EXPECT_GT(
        virtual_chunk_offset_t(2, 10, 1), virtual_chunk_offset_t(4, 50, 0));
}

TEST(VirtualOffsetTest, use_virtual_offset_as_map_key)
{
    ankerl::unordered_dense::segmented_map<
        virtual_chunk_offset_t,
        int,
        virtual_chunk_offset_t_hasher>
        map;

    map[virtual_chunk_offset_t(2, 0, 1)] = 1;
    map[virtual_chunk_offset_t(2, 0, 0)] = 2;
    ASSERT_TRUE(map.contains(virtual_chunk_offset_t(2, 0, 1)));
    EXPECT_EQ(map[virtual_chunk_offset_t(2, 0, 1)], 1);
    ASSERT_TRUE(map.contains(virtual_chunk_offset_t(2, 0, 0)));
    EXPECT_EQ(map[virtual_chunk_offset_t(2, 0, 0)], 2);
}

TEST(VirtualOffsetTest, compact_conversion)
{
    // compact_virtual_chunk_offset_t truncates the low 16 bits of raw(),
    // preserving count above the high 12 bits of offset.
    virtual_chunk_offset_t const v1(5, 0x1234567, 0);
    compact_virtual_chunk_offset_t const c1(v1);
    EXPECT_EQ(c1.get_count(), 5U);

    // Two offsets differing only in the low 16 bits of raw() should
    // compact to the same value.
    virtual_chunk_offset_t const v2(5, 0x1230000, 0);
    virtual_chunk_offset_t const v3(5, 0x123FFFF, 0);
    compact_virtual_chunk_offset_t const c2(v2);
    compact_virtual_chunk_offset_t const c3(v3);
    EXPECT_EQ(c2, c3);

    virtual_chunk_offset_t const v4(6, 0x1234567, 0);
    compact_virtual_chunk_offset_t const c4(v4);
    EXPECT_NE(c1, c4);
    EXPECT_EQ(c4.get_count(), 6U);

    EXPECT_GT(c4, c1);

    // is_in_fast_list does not affect compact conversion.
    virtual_chunk_offset_t const v5(5, 0x1234567, 1);
    compact_virtual_chunk_offset_t const c5(v5);
    EXPECT_EQ(c1, c5);

    virtual_chunk_offset_t const v6(
        virtual_chunk_offset_t::MAX_COUNT,
        virtual_chunk_offset_t::MAX_OFFSET,
        0);
    EXPECT_NE(
        compact_virtual_chunk_offset_t(v6), INVALID_COMPACT_VIRTUAL_OFFSET);
}

TEST(WideOffsets, virtual_offset_holds_35_bit_counts)
{
    uint64_t const count = (1ull << 35) - 2;
    virtual_chunk_offset_t const v{count, 0x0fffffff, 1};
    EXPECT_EQ(v.count, count);
    EXPECT_EQ(INVALID_VIRTUAL_OFFSET.count, virtual_chunk_offset_t::MAX_COUNT);
}

TEST(WideOffsets, compact_offset_keeps_wide_counts_and_orders_them)
{
    static_assert(sizeof(compact_virtual_chunk_offset_t) == 8);
    compact_virtual_chunk_offset_t const a{
        virtual_chunk_offset_t{(1u << 20) - 1, 0x10000, 1}};
    compact_virtual_chunk_offset_t const b{
        virtual_chunk_offset_t{1u << 20, 0, 1}};
    EXPECT_EQ(b.get_count(), 1u << 20);
    EXPECT_EQ(static_cast<uint64_t>(a), (uint64_t{(1u << 20) - 1} << 12) | 1);
    EXPECT_LT(a, b);
}

TEST(WideOffsets, legacy_values_widen_with_invalid_preserved)
{
    using C = compact_virtual_chunk_offset_t;
    EXPECT_EQ(C::from_legacy(0xFFFFFFFF), INVALID_COMPACT_VIRTUAL_OFFSET);
    EXPECT_EQ(C::from_legacy(0), MIN_COMPACT_VIRTUAL_OFFSET);
    EXPECT_EQ(static_cast<uint64_t>(C::from_legacy(0x12345678)), 0x12345678u);
    EXPECT_EQ(INVALID_COMPACT_VIRTUAL_OFFSET.to_legacy(), 0xFFFFFFFFu);
}

TEST(WideOffsets, offset_pair_round_trips_sixteen_bytes_and_reads_eight)
{
    static_assert(sizeof(compact_offset_pair) == 16);
    compact_offset_pair const p{
        compact_virtual_chunk_offset_t{
            virtual_chunk_offset_t{1u << 20, 0x20000, 1}},
        INVALID_COMPACT_VIRTUAL_OFFSET};
    EXPECT_EQ(p.serialize().size(), 16u);
    EXPECT_EQ(compact_offset_pair::deserialize(p.serialize()), p);
    monad::byte_string const legacy{0x05, 0x01, 0, 0, 0xff, 0xff, 0xff, 0xff};
    auto const q = compact_offset_pair::deserialize(legacy);
    EXPECT_EQ(static_cast<uint64_t>(q.fast), 0x105u);
    EXPECT_EQ(q.slow, INVALID_COMPACT_VIRTUAL_OFFSET);
}

TEST(WideOffsets, legacy_writer_emits_eight_bytes)
{
    compact_offset_pair const p{
        compact_virtual_chunk_offset_t::from_legacy(0x105),
        INVALID_COMPACT_VIRTUAL_OFFSET};
    monad::byte_string const expected{0x05, 0x01, 0, 0, 0xff, 0xff, 0xff, 0xff};
    EXPECT_EQ(p.serialize_legacy(), expected);
}
