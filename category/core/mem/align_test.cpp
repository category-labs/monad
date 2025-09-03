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

#include <category/core/mem/align.h>

#include <gtest/gtest.h>

TEST(align, bit_round_up)
{
    EXPECT_EQ(monad_bit_round_up(0, 0), 0);
    EXPECT_EQ(monad_bit_round_up(0, 1), 0);
    EXPECT_EQ(monad_bit_round_up(0, 2), 0);

    EXPECT_EQ(monad_bit_round_up(1, 0), 1);
    EXPECT_EQ(monad_bit_round_up(1, 1), 2);
    EXPECT_EQ(monad_bit_round_up(1, 2), 4);

    EXPECT_EQ(monad_bit_round_up(2, 0), 2);
    EXPECT_EQ(monad_bit_round_up(2, 1), 2);
    EXPECT_EQ(monad_bit_round_up(2, 2), 4);
}

TEST(align, round_size_to_align)
{
    EXPECT_EQ(monad_round_size_to_align(7, 1), 7);
    EXPECT_EQ(monad_round_size_to_align(8, 1), 8);
    EXPECT_EQ(monad_round_size_to_align(9, 1), 9);

    EXPECT_EQ(monad_round_size_to_align(7, 4), 8);
    EXPECT_EQ(monad_round_size_to_align(8, 4), 8);
    EXPECT_EQ(monad_round_size_to_align(9, 4), 12);

    EXPECT_EQ(monad_round_size_to_align(7, 8), 8);
    EXPECT_EQ(monad_round_size_to_align(8, 8), 8);
    EXPECT_EQ(monad_round_size_to_align(9, 8), 16);
}
