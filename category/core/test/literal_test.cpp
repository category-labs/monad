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

#include <category/core/byte_string.hpp>
#include <category/core/hex_literal.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp>  // NOLINT

using namespace ::monad::literals;

TEST(LiteralTest, variable_length_hex)
{
    EXPECT_EQ((0x123456781234567812345678_hex).size(), 12);
    EXPECT_EQ(
        0x123456781234567812345678_hex,
        monad::byte_string({
            0x12,
            0x34,
            0x56,
            0x78,
            0x12,
            0x34,
            0x56,
            0x78,
            0x12,
            0x34,
            0x56,
            0x78,
        }));

    EXPECT_EQ(
        (0x123456781234567812345678123456781234567812345678_hex).size(), 24);
    EXPECT_EQ(
        0x123456781234567812345678123456781234567812345678_hex,
        monad::byte_string({
            0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78,
            0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78,
            0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78,
        }));

    EXPECT_EQ(
        (0x1234567812345678123456781234567812345678123456781234567812345678_hex)
            .size(),
        32);
    EXPECT_EQ(
        0x1234567812345678123456781234567812345678123456781234567812345678_hex,
        monad::byte_string({
            0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56,
            0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34,
            0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78,
        }));

    // without 0x prefix
    EXPECT_EQ(
        (1234567812345678123456781234567812345678123456781234567812345678_hex)
            .size(),
        32);
    EXPECT_EQ(
        1234567812345678123456781234567812345678123456781234567812345678_hex,
        monad::byte_string({
            0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56,
            0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34,
            0x56, 0x78, 0x12, 0x34, 0x56, 0x78, 0x12, 0x34, 0x56, 0x78,
        }));

    // odd number of nibbles
    EXPECT_EQ(
        0x12345678123456781234567_hex,
        monad::byte_string(
            {0x01,
             0x23,
             0x45,
             0x67,
             0x81,
             0x23,
             0x45,
             0x67,
             0x81,
             0x23,
             0x45,
             0x67}));
}