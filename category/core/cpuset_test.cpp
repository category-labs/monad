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

#include <gtest/gtest.h>

#include <category/core/cleanup.h> // NOLINT(misc-include-cleaner)
#include <category/core/cpuset.h>

#include <sched.h>
#include <string.h>

TEST(Cpuset, parse_all)
{
    char *const all [[gnu::cleanup(cleanup_free)]] = strdup("0-15");
    auto set = monad_parse_cpuset(all);
    for (int i = 0; i <= 15; ++i) {
        EXPECT_TRUE(static_cast<bool>(CPU_ISSET(i, &set)));
    }
}

TEST(Cpuset, parse_union)
{
    char *const some1 [[gnu::cleanup(cleanup_free)]] = strdup("0,1-7");
    auto set1 = monad_parse_cpuset(some1);
    EXPECT_TRUE(static_cast<bool>(CPU_ISSET(0, &set1)));
    for (int i = 1; i <= 7; ++i) {
        EXPECT_TRUE(static_cast<bool>(CPU_ISSET(i, &set1)));
    }

    char *const some2 [[gnu::cleanup(cleanup_free)]] = strdup("0-1,5-10");
    auto set2 = monad_parse_cpuset(some2);
    EXPECT_TRUE(static_cast<bool>(CPU_ISSET(0, &set2)));
    for (int i = 0; i <= 1; ++i) {
        EXPECT_TRUE(static_cast<bool>(CPU_ISSET(i, &set2)));
    }
    for (int i = 5; i <= 10; ++i) {
        EXPECT_TRUE(static_cast<bool>(CPU_ISSET(i, &set2)));
    }
}

TEST(Cpuset, parse_disjoint)
{
    char *const evens [[gnu::cleanup(cleanup_free)]] =
        strdup("0,2,4,6,8,10,12,14");
    auto set = monad_parse_cpuset(evens);
    for (int i = 0; i <= 14; i += 2) {
        EXPECT_TRUE(static_cast<bool>(CPU_ISSET(i, &set)));
    }
}

TEST(Cpuset, parse_empty)
{
    cpu_set_t empty;
    CPU_ZERO(&empty);
    char *const evens [[gnu::cleanup(cleanup_free)]] = strdup("");
    auto set = monad_parse_cpuset(evens);
    EXPECT_TRUE(CPU_EQUAL(&empty, &set));
}
