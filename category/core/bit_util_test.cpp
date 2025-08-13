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

#include <category/core/bit_util.h>

#include <gtest/gtest.h>

TEST(bit_util, div_floor)
{
    EXPECT_EQ(bit_div_floor(0, 0), 0);
    EXPECT_EQ(bit_div_floor(0, 1), 0);
    EXPECT_EQ(bit_div_floor(0, 2), 0);

    EXPECT_EQ(bit_div_floor(1, 0), 1);
    EXPECT_EQ(bit_div_floor(1, 1), 0);
    EXPECT_EQ(bit_div_floor(1, 2), 0);

    EXPECT_EQ(bit_div_floor(2, 0), 2);
    EXPECT_EQ(bit_div_floor(2, 1), 1);
    EXPECT_EQ(bit_div_floor(2, 2), 0);
}

TEST(bit_util, div_ceil)
{
    EXPECT_EQ(bit_div_ceil(0, 0), 0);
    EXPECT_EQ(bit_div_ceil(0, 1), 0);
    EXPECT_EQ(bit_div_ceil(0, 2), 0);

    EXPECT_EQ(bit_div_ceil(1, 0), 1);
    EXPECT_EQ(bit_div_ceil(1, 1), 1);
    EXPECT_EQ(bit_div_ceil(1, 2), 1);

    EXPECT_EQ(bit_div_ceil(2, 0), 2);
    EXPECT_EQ(bit_div_ceil(2, 1), 1);
    EXPECT_EQ(bit_div_ceil(2, 2), 1);
}

TEST(bit_util, round_down)
{
    EXPECT_EQ(bit_round_down(0, 0), 0);
    EXPECT_EQ(bit_round_down(0, 1), 0);
    EXPECT_EQ(bit_round_down(0, 2), 0);

    EXPECT_EQ(bit_round_down(1, 0), 1);
    EXPECT_EQ(bit_round_down(1, 1), 0);
    EXPECT_EQ(bit_round_down(1, 2), 0);

    EXPECT_EQ(bit_round_down(2, 0), 2);
    EXPECT_EQ(bit_round_down(2, 1), 2);
    EXPECT_EQ(bit_round_down(2, 2), 0);
}

TEST(bit_util, round_up)
{
    EXPECT_EQ(bit_round_up(0, 0), 0);
    EXPECT_EQ(bit_round_up(0, 1), 0);
    EXPECT_EQ(bit_round_up(0, 2), 0);

    EXPECT_EQ(bit_round_up(1, 0), 1);
    EXPECT_EQ(bit_round_up(1, 1), 2);
    EXPECT_EQ(bit_round_up(1, 2), 4);

    EXPECT_EQ(bit_round_up(2, 0), 2);
    EXPECT_EQ(bit_round_up(2, 1), 2);
    EXPECT_EQ(bit_round_up(2, 2), 4);
}
