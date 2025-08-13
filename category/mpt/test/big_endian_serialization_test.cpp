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

#include <category/core/hex_literal.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/util.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <cstdint>
#include <stdexcept>

using namespace monad::mpt;
using namespace monad::literals;

TEST(serialize_to_big_endian, test)
{
    uint64_t const n = 0x1122334455667788;
    EXPECT_EQ(serialize_as_big_endian<8>(n), 0x1122334455667788_hex);
    EXPECT_EQ(serialize_as_big_endian<6>(n), 0x334455667788_hex);
    EXPECT_EQ(serialize_as_big_endian<2>(n), 0x7788_hex);

    uint32_t const n2 = 0x11223344;
    EXPECT_EQ(serialize_as_big_endian<4>(n2), 0x11223344_hex);
    EXPECT_EQ(serialize_as_big_endian<2>(n2), 0x3344_hex);
}

TEST(deserialize_from_big_endian_nibbles, test)
{
    Nibbles const a{0x00112233_hex};
    EXPECT_EQ(deserialize_from_big_endian<uint32_t>(a), 0x112233);

    Nibbles const b{0x112233_hex};
    EXPECT_EQ(deserialize_from_big_endian<uint32_t>(b), 0x112233);

    Nibbles const c{0xaabbccdd00112233_hex};
    EXPECT_THROW(deserialize_from_big_endian<uint8_t>(c), std::runtime_error);
    EXPECT_THROW(deserialize_from_big_endian<uint16_t>(c), std::runtime_error);
    EXPECT_THROW(deserialize_from_big_endian<uint32_t>(c), std::runtime_error);
    EXPECT_EQ(deserialize_from_big_endian<uint64_t>(c), 0xaabbccdd00112233);
}
