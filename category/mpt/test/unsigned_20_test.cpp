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

#include "gtest/gtest.h"

#include <category/mpt/config.hpp>
#include <category/mpt/detail/unsigned_20.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <cstdint>
#include <type_traits>

TEST(unsigned_20, works)
{
    using MONAD_MPT_NAMESPACE::detail::unsigned_20;

    unsigned_20 a(5);
    unsigned_20 const b(6);
    EXPECT_EQ(b - a, 1);
    EXPECT_EQ(a - b, 0xfffff);

    a |= 0xffffffff;
    EXPECT_EQ(a, 0xfffff);
    a += 1;
    EXPECT_EQ(a, 0);

    a = 1 << 19;
    EXPECT_EQ(a, 1 << 19);
    a <<= 1;
    EXPECT_EQ(a, 0);

    a = 0;
    a -= 1;
    EXPECT_EQ(a, 0xfffff);

    // Make sure this follows C's deeply unhelpful integer promotion rules
    static_assert(std::is_same_v<decltype(a + 1), int>);
    static_assert(std::is_same_v<decltype(a + 1U), unsigned>);
    static_assert(std::is_same_v<decltype(a + int16_t(1)), unsigned_20>);
    static_assert(std::is_same_v<decltype(a + uint16_t(1)), unsigned_20>);
}
