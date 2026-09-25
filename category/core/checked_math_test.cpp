// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/checked_math.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <limits>

using namespace monad;

TEST(CheckedMath, Add)
{
    auto const sum = checked_add(uint256_t{1}, uint256_t{2});
    ASSERT_TRUE(sum);
    EXPECT_EQ(sum.assume_value(), uint256_t{3});

    auto const overflow =
        checked_add(std::numeric_limits<uint256_t>::max(), uint256_t{1});
    ASSERT_TRUE(overflow.has_error());
    EXPECT_EQ(overflow.error(), MathError::Overflow);
}

TEST(CheckedMath, Subtract)
{
    auto const difference = checked_sub(uint256_t{3}, uint256_t{2});
    ASSERT_TRUE(difference);
    EXPECT_EQ(difference.assume_value(), uint256_t{1});

    auto const underflow = checked_sub(uint256_t{0}, uint256_t{1});
    ASSERT_TRUE(underflow.has_error());
    EXPECT_EQ(underflow.error(), MathError::Underflow);
}

TEST(CheckedMath, Multiply)
{
    constexpr uint256_t TWO_TO_128 = uint256_t{1} << 128;

    auto const product = checked_mul(TWO_TO_128 - 1, TWO_TO_128 + 1);
    ASSERT_TRUE(product);
    EXPECT_EQ(product.assume_value(), std::numeric_limits<uint256_t>::max());

    auto const overflow = checked_mul(TWO_TO_128, TWO_TO_128);
    ASSERT_TRUE(overflow.has_error());
    EXPECT_EQ(overflow.error(), MathError::Overflow);
}

TEST(CheckedMath, MultiplyDivide)
{
    auto const rounded =
        checked_wide_mul_div(uint256_t{7}, uint256_t{5}, uint256_t{3});
    ASSERT_TRUE(rounded);
    EXPECT_EQ(rounded.assume_value(), uint256_t{11});

    auto const zero =
        checked_wide_mul_div(uint256_t{0}, uint256_t{5}, uint256_t{3});
    ASSERT_TRUE(zero);
    EXPECT_EQ(zero.assume_value(), uint256_t{0});

    auto const below_one =
        checked_wide_mul_div(uint256_t{2}, uint256_t{3}, uint256_t{7});
    ASSERT_TRUE(below_one);
    EXPECT_EQ(below_one.assume_value(), uint256_t{0});
}

TEST(CheckedMath, MultiplyDivideWideProduct)
{
    auto const max = std::numeric_limits<uint256_t>::max();
    auto const quotient = checked_wide_mul_div(max, max, max);
    ASSERT_TRUE(quotient);
    EXPECT_EQ(quotient.assume_value(), max);

    constexpr auto half = uint256_t{1} << 255;
    auto const rounded = checked_wide_mul_div(max, half, half + 1);
    ASSERT_TRUE(rounded);
    EXPECT_EQ(rounded.assume_value(), max - 2);

    auto const overflow = checked_wide_mul_div(max, max, max - 1);
    ASSERT_TRUE(overflow.has_error());
    EXPECT_EQ(overflow.error(), MathError::Overflow);
}

TEST(CheckedMath, MultiplyDivideByZero)
{
    for (auto const x : {uint256_t{0}, std::numeric_limits<uint256_t>::max()}) {
        auto const result = checked_wide_mul_div(x, x, uint256_t{0});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), MathError::DivisionByZero);
    }
}

TEST(CheckedMath, Divide)
{
    auto const quotient = checked_div(uint256_t{7}, uint256_t{2});
    ASSERT_TRUE(quotient);
    EXPECT_EQ(quotient.assume_value(), uint256_t{3});

    auto const division_by_zero = checked_div(uint256_t{1}, uint256_t{0});
    ASSERT_TRUE(division_by_zero.has_error());
    EXPECT_EQ(division_by_zero.error(), MathError::DivisionByZero);
}
