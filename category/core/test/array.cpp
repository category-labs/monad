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

#include <category/core/array.hpp>

#include <category/core/config.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp>  // NOLINT

#include <gtest/gtest.h>

#include <utility>

namespace
{
    TEST(ArrayTest, make_array_of_immovable)
    {
        struct Foo
        {
            int x;
            Foo(int a, int b)
                : x(a + b)
            {
            }
            Foo(Foo const &) = delete;
            Foo(Foo &&) = delete;
            Foo &operator=(Foo const &) = delete;
            Foo &operator=(Foo &&) = delete;
        };
        auto arr =
            MONAD_NAMESPACE::make_array<Foo, 5>(std::piecewise_construct, 2, 3);
        EXPECT_EQ(arr.size(), 5);
        EXPECT_EQ(arr[0].x, 5);
        EXPECT_EQ(arr[1].x, 5);
        EXPECT_EQ(arr[2].x, 5);
        EXPECT_EQ(arr[3].x, 5);
        EXPECT_EQ(arr[4].x, 5);
    }
}
