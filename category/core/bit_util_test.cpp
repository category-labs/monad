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
