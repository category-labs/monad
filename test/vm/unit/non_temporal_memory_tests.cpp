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

#include <category/core/runtime/non_temporal_memory.hpp>

#include <cstring>

#include <gtest/gtest.h>

using namespace monad::vm::runtime;

TEST(non_temporal_memory, bzero_0)
{
    non_temporal_bzero(nullptr, 0);
    alignas(32) uint8_t x;
    non_temporal_bzero(&x, 0);
}

TEST(non_temporal_memory, bzero_32)
{
    static constexpr size_t N = 32;

    alignas(32) uint8_t x[N];
    std::memset(x, 1, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 1; }));

    non_temporal_bzero(&x, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 0; }));
}

TEST(non_temporal_memory, bzero_160)
{
    static constexpr size_t N = 160;

    alignas(32) uint8_t x[N];
    std::memset(x, 1, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 1; }));

    non_temporal_bzero(&x, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 0; }));
}

TEST(non_temporal_memory, memcpy_0)
{
    alignas(32) uint8_t x;
    alignas(32) uint8_t y;
    non_temporal_memcpy(nullptr, nullptr, 0);
    non_temporal_memcpy(&x, nullptr, 0);
    non_temporal_memcpy(nullptr, &y, 0);
    non_temporal_memcpy(&x, &y, 0);
}

TEST(non_temporal_memory, memcpy_32)
{
    static constexpr size_t N = 32;

    alignas(32) uint8_t x[N];
    alignas(32) uint8_t y[N];
    std::memset(x, 1, N);
    std::memset(y, 2, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 1; }));
    ASSERT_TRUE(std::all_of(
        std::begin(y), std::end(y), [](auto const b) { return b == 2; }));

    non_temporal_memcpy(&y, &x, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 1; }));
    ASSERT_TRUE(std::all_of(
        std::begin(y), std::end(y), [](auto const b) { return b == 1; }));
}

TEST(non_temporal_memory, memcpy_160)
{
    static constexpr size_t N = 160;

    alignas(32) uint8_t x[N];
    alignas(32) uint8_t y[N];
    std::memset(x, 1, N);
    std::memset(y, 2, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 1; }));
    ASSERT_TRUE(std::all_of(
        std::begin(y), std::end(y), [](auto const b) { return b == 2; }));

    non_temporal_memcpy(&y, &x, N);
    ASSERT_TRUE(std::all_of(
        std::begin(x), std::end(x), [](auto const b) { return b == 1; }));
    ASSERT_TRUE(std::all_of(
        std::begin(y), std::end(y), [](auto const b) { return b == 1; }));
}
