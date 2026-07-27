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

#include <category/core/seeded_fast_hash.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#include <komihash.h>
#pragma GCC diagnostic pop

#include <gtest/gtest.h>

#include <cstdint>
#include <unistd.h>

using namespace monad;

// The seed is applied per process. Unfortunately this makes the test suite
// fairly arcane, since we need to create a death test for each case and
// communicate success via error codes.
TEST(SeededFastHashDeathTest, unseeded_process_uses_default)
{
    EXPECT_EXIT(
        ({
            // default is 143
            unsigned char const data[] = {1, 2, 3, 4};
            ::_exit(
                seeded_fast_hash(data, sizeof(data)) ==
                        komihash(data, sizeof(data), 143)
                    ? 0
                    : 1);
        }),
        ::testing::ExitedWithCode(0),
        "");
}

TEST(SeededFastHashDeathTest, seed_is_set_once)
{
    EXPECT_EXIT(
        ({
            unsigned char const data[] = {1, 2, 3, 4};
            uint64_t const seed = set_hash_seed();
            // yes, this is flaky, but would be 10^13 years to trigger, and the
            // coverage is worth it.
            if (seed == 143) {
                ::_exit(1);
            }
            if (seeded_fast_hash(data, sizeof(data)) !=
                komihash(data, sizeof(data), seed)) {
                ::_exit(2);
            }
            // later attempts are ignored
            if (set_hash_seed() != seed) {
                ::_exit(3);
            }
            if (seeded_fast_hash(data, sizeof(data)) !=
                komihash(data, sizeof(data), seed)) {
                ::_exit(4);
            }
            ::_exit(0);
        }),
        ::testing::ExitedWithCode(0),
        "");
}

TEST(SeededFastHashDeathTest, seed_after_use_is_ignored)
{
    EXPECT_EXIT(
        ({
            unsigned char const data[] = {1, 2, 3, 4};
            if (seeded_fast_hash(data, sizeof(data)) !=
                komihash(data, sizeof(data), 143)) {
                ::_exit(1);
            }
            if (set_hash_seed() != 143) {
                ::_exit(2);
            }
            if (seeded_fast_hash(data, sizeof(data)) !=
                komihash(data, sizeof(data), 143)) {
                ::_exit(3);
            }
            ::_exit(0);
        }),
        ::testing::ExitedWithCode(0),
        "");
}
