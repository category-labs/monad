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
