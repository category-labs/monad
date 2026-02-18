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

#include <category/mpt/util.hpp>

#include <ankerl/unordered_dense.h>

#include <gtest/gtest.h>

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
    ASSERT_TRUE(map.find(virtual_chunk_offset_t(2, 0, 1)) != map.end());
    EXPECT_EQ(map[virtual_chunk_offset_t(2, 0, 1)], 1);
    ASSERT_TRUE(map.find(virtual_chunk_offset_t(2, 0, 0)) != map.end());
    EXPECT_EQ(map[virtual_chunk_offset_t(2, 0, 0)], 2);
}

TEST(VirtualOffsetTest, compact_conversion)
{
    // compact_virtual_chunk_offset_t truncates the low 16 bits of raw(),
    // preserving count in the top 20 bits and the high 12 bits of offset.
    virtual_chunk_offset_t const v1(5, 0x1234567, 0, 0);
    compact_virtual_chunk_offset_t const c1(v1);
    EXPECT_EQ(c1.get_count(), 5U);

    // Two offsets differing only in the low 16 bits of raw() should
    // compact to the same value.
    virtual_chunk_offset_t const v2(5, 0x1230000, 0, 0);
    virtual_chunk_offset_t const v3(5, 0x123FFFF, 0, 0);
    compact_virtual_chunk_offset_t const c2(v2);
    compact_virtual_chunk_offset_t const c3(v3);
    EXPECT_EQ(c2, c3);

    virtual_chunk_offset_t const v4(6, 0x1234567, 0, 0);
    compact_virtual_chunk_offset_t const c4(v4);
    EXPECT_NE(c1, c4);
    EXPECT_EQ(c4.get_count(), 6U);

    EXPECT_GT(c4, c1);

    // spare and is_in_fast_list do not affect compact conversion.
    virtual_chunk_offset_t const v5(5, 0x1234567, 1, 100);
    compact_virtual_chunk_offset_t const c5(v5);
    EXPECT_EQ(c1, c5);

    // max virtual offset's compact representation collides with
    // INVALID_COMPACT_VIRTUAL_OFFSET. This is why the insertion count assertion
    // in db_metadata::append_() uses strict less-than to prevent
    // insertion_count from reaching MAX_COUNT.
    virtual_chunk_offset_t const v6(
        virtual_chunk_offset_t::MAX_COUNT,
        virtual_chunk_offset_t::MAX_OFFSET,
        0,
        0);
    EXPECT_EQ(
        compact_virtual_chunk_offset_t(v6), INVALID_COMPACT_VIRTUAL_OFFSET);
}
