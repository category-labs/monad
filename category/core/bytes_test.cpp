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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <evmc/evmc.h>

#include <cstdint>
#include <unordered_set>

using namespace monad;
using namespace monad::literals;

// ---------------------------------------------------------------------------
// Default constructor
// ---------------------------------------------------------------------------

TEST(Bytes32, default_constructor_is_zero)
{
    constexpr bytes32_t zero;
    for (auto const b : zero.bytes) {
        EXPECT_EQ(b, 0);
    }
}

// ---------------------------------------------------------------------------
// uint64_t constructor — big-endian in the last 8 bytes
// ---------------------------------------------------------------------------

TEST(Bytes32, uint64_constructor_big_endian)
{
    constexpr bytes32_t val{uint64_t{0x0102030405060708}};

    // Leading 24 bytes must be zero.
    for (int i = 0; i < 24; ++i) {
        EXPECT_EQ(val.bytes[i], 0) << "byte " << i;
    }

    EXPECT_EQ(val.bytes[24], 0x01);
    EXPECT_EQ(val.bytes[25], 0x02);
    EXPECT_EQ(val.bytes[26], 0x03);
    EXPECT_EQ(val.bytes[27], 0x04);
    EXPECT_EQ(val.bytes[28], 0x05);
    EXPECT_EQ(val.bytes[29], 0x06);
    EXPECT_EQ(val.bytes[30], 0x07);
    EXPECT_EQ(val.bytes[31], 0x08);
}

TEST(Bytes32, uint64_constructor_zero)
{
    constexpr bytes32_t val{uint64_t{0}};
    constexpr bytes32_t zero;
    EXPECT_EQ(val, zero);
}

TEST(Bytes32, uint64_constructor_one)
{
    constexpr bytes32_t val{uint64_t{1}};
    EXPECT_EQ(val.bytes[31], 1);
    for (int i = 0; i < 31; ++i) {
        EXPECT_EQ(val.bytes[i], 0);
    }
}

// ---------------------------------------------------------------------------
// Variadic byte constructor
// ---------------------------------------------------------------------------

TEST(Bytes32, variadic_byte_constructor)
{
    constexpr bytes32_t val{uint8_t{0xAA}, uint8_t{0xBB}, uint8_t{0xCC}};

    EXPECT_EQ(val.bytes[0], 0xAA);
    EXPECT_EQ(val.bytes[1], 0xBB);
    EXPECT_EQ(val.bytes[2], 0xCC);
    for (int i = 3; i < 32; ++i) {
        EXPECT_EQ(val.bytes[i], 0) << "byte " << i;
    }
}

// ---------------------------------------------------------------------------
// operator bool
// ---------------------------------------------------------------------------

TEST(Bytes32, operator_bool_zero_is_false)
{
    constexpr bytes32_t zero;
    EXPECT_FALSE(static_cast<bool>(zero));
}

TEST(Bytes32, operator_bool_nonzero_is_true)
{
    constexpr bytes32_t val{uint64_t{1}};
    EXPECT_TRUE(static_cast<bool>(val));
}

// ---------------------------------------------------------------------------
// Equality and ordering
// ---------------------------------------------------------------------------

TEST(Bytes32, equality)
{
    constexpr auto a = bytes32_from_hex(
        "0000000000000000000000000000000000000000000000000000000000000001");
    constexpr auto b = bytes32_from_hex(
        "0000000000000000000000000000000000000000000000000000000000000001");
    constexpr bytes32_t c{uint64_t{2}};
    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

TEST(Bytes32, ordering)
{
    constexpr bytes32_t a{uint64_t{1}};
    constexpr bytes32_t b{uint64_t{2}};
    EXPECT_LT(a, b);
    EXPECT_GT(b, a);
    EXPECT_LE(a, a);
    EXPECT_GE(b, b);
}

TEST(Bytes32, ordering_lexicographic)
{
    // A value with a higher first byte should compare greater,
    // regardless of trailing bytes.
    constexpr bytes32_t high{uint8_t{0xFF}};
    constexpr bytes32_t low{uint64_t{UINT64_MAX}};
    EXPECT_GT(high, low);
}

// ---------------------------------------------------------------------------
// _bytes32 literal
// ---------------------------------------------------------------------------

TEST(Bytes32, literal_parses_correctly)
{
    constexpr auto val =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr bytes32_t expected{uint64_t{1}};
    EXPECT_EQ(val, expected);
}

TEST(Bytes32, literal_full_width)
{
    constexpr auto val =
        0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_bytes32;
    for (int i = 0; i < 32; i += 4) {
        EXPECT_EQ(val.bytes[i + 0], 0xDE);
        EXPECT_EQ(val.bytes[i + 1], 0xAD);
        EXPECT_EQ(val.bytes[i + 2], 0xBE);
        EXPECT_EQ(val.bytes[i + 3], 0xEF);
    }
}

// ---------------------------------------------------------------------------
// bytes32_from_hex
// ---------------------------------------------------------------------------

TEST(Bytes32, from_hex_without_prefix)
{
    auto const val = bytes32_from_hex(
        "0000000000000000000000000000000000000000000000000000000000000042");
    EXPECT_EQ(val.bytes[31], 0x42);
}

TEST(Bytes32, from_hex_with_prefix)
{
    auto const val = bytes32_from_hex(
        "0x0000000000000000000000000000000000000000000000000000000000000042");
    EXPECT_EQ(val.bytes[31], 0x42);
}

// ---------------------------------------------------------------------------
// Well-known constants
// ---------------------------------------------------------------------------

TEST(Bytes32, null_hash_is_nonzero)
{
    EXPECT_TRUE(static_cast<bool>(NULL_HASH));
}

TEST(Bytes32, null_root_is_nonzero)
{
    EXPECT_TRUE(static_cast<bool>(NULL_ROOT));
}

// ---------------------------------------------------------------------------
// Hashing — std::hash, ankerl, boost
// ---------------------------------------------------------------------------

TEST(Bytes32, std_hash_equal_values_same_hash)
{
    bytes32_t const a{uint64_t{42}};
    bytes32_t const b{uint64_t{42}};
    EXPECT_EQ(std::hash<bytes32_t>{}(a), std::hash<bytes32_t>{}(b));
}

TEST(Bytes32, std_hash_different_values_differ)
{
    bytes32_t const a{uint64_t{1}};
    bytes32_t const b{uint64_t{2}};
    // Not guaranteed by spec, but overwhelmingly likely for a good hash.
    EXPECT_NE(std::hash<bytes32_t>{}(a), std::hash<bytes32_t>{}(b));
}

TEST(Bytes32, ankerl_hash_consistent_with_std)
{
    bytes32_t const val{uint64_t{123}};
    auto const std_h = std::hash<bytes32_t>{}(val);
    auto const ankerl_h = ankerl::unordered_dense::hash<bytes32_t>{}(val);
    EXPECT_EQ(std_h, ankerl_h);
}

TEST(Bytes32, boost_hash_consistent_with_std)
{
    bytes32_t const val{uint64_t{456}};
    auto const std_h = std::hash<bytes32_t>{}(val);
    auto const boost_h = boost::hash_value(val);
    EXPECT_EQ(std_h, boost_h);
}

TEST(Bytes32, usable_in_unordered_set)
{
    std::unordered_set<bytes32_t> set;
    set.insert(bytes32_t{uint64_t{1}});
    set.insert(bytes32_t{uint64_t{2}});
    set.insert(bytes32_t{uint64_t{1}});
    EXPECT_EQ(set.size(), 2);
}

// ---------------------------------------------------------------------------
// evmc_bytes32 implicit conversion
// ---------------------------------------------------------------------------

TEST(Bytes32, implicit_from_evmc_bytes32)
{
    evmc_bytes32 raw{};
    raw.bytes[31] = 0x07;
    bytes32_t const wrapped = raw;
    EXPECT_EQ(wrapped.bytes[31], 0x07);
}

// ---------------------------------------------------------------------------
// byte_string_view conversion
// ---------------------------------------------------------------------------

TEST(Bytes32, converts_to_byte_string_view)
{
    bytes32_t const val{uint64_t{0xFF}};
    byte_string_view const view = val;
    EXPECT_EQ(view.size(), 32);
    EXPECT_EQ(view[31], 0xFF);
}
