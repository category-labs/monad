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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

#include <evmc/evmc.h>

#include <cstdint>
#include <type_traits>
#include <unordered_set>

using namespace monad;
using namespace monad::literals;

// ---------------------------------------------------------------------------
// Default constructor
// ---------------------------------------------------------------------------

TEST(Address, default_constructor_is_zero)
{
    constexpr Address zero;
    for (auto const b : zero.bytes) {
        EXPECT_EQ(b, 0);
    }
}

// ---------------------------------------------------------------------------
// uint64_t constructor — big-endian in the last 8 bytes
// ---------------------------------------------------------------------------

TEST(Address, uint64_constructor_big_endian)
{
    constexpr Address val{uint64_t{0x0102030405060708}};

    // Leading 12 bytes must be zero.
    for (int i = 0; i < 12; ++i) {
        EXPECT_EQ(val.bytes[i], 0) << "byte " << i;
    }

    EXPECT_EQ(val.bytes[12], 0x01);
    EXPECT_EQ(val.bytes[13], 0x02);
    EXPECT_EQ(val.bytes[14], 0x03);
    EXPECT_EQ(val.bytes[15], 0x04);
    EXPECT_EQ(val.bytes[16], 0x05);
    EXPECT_EQ(val.bytes[17], 0x06);
    EXPECT_EQ(val.bytes[18], 0x07);
    EXPECT_EQ(val.bytes[19], 0x08);
}

TEST(Address, uint64_constructor_zero)
{
    constexpr Address val{uint64_t{0}};
    constexpr Address zero;
    EXPECT_EQ(val, zero);
}

TEST(Address, uint64_constructor_one)
{
    constexpr Address val{uint64_t{1}};
    EXPECT_EQ(val.bytes[19], 1);
    for (int i = 0; i < 19; ++i) {
        EXPECT_EQ(val.bytes[i], 0);
    }
}

// ---------------------------------------------------------------------------
// Variadic byte constructor
// ---------------------------------------------------------------------------

TEST(Address, variadic_byte_constructor)
{
    constexpr Address val{uint8_t{0xAA}, uint8_t{0xBB}, uint8_t{0xCC}};

    EXPECT_EQ(val.bytes[0], 0xAA);
    EXPECT_EQ(val.bytes[1], 0xBB);
    EXPECT_EQ(val.bytes[2], 0xCC);
    for (int i = 3; i < 20; ++i) {
        EXPECT_EQ(val.bytes[i], 0) << "byte " << i;
    }
}

// ---------------------------------------------------------------------------
// operator bool
// ---------------------------------------------------------------------------

TEST(Address, operator_bool_zero_is_false)
{
    constexpr Address zero;
    EXPECT_FALSE(static_cast<bool>(zero));
}

TEST(Address, operator_bool_nonzero_is_true)
{
    constexpr Address val{uint64_t{1}};
    EXPECT_TRUE(static_cast<bool>(val));
}

// ---------------------------------------------------------------------------
// Equality and ordering
// ---------------------------------------------------------------------------

TEST(Address, equality)
{
    constexpr auto a =
        address_from_hex("0000000000000000000000000000000000000001");
    constexpr auto b =
        address_from_hex("0000000000000000000000000000000000000001");
    constexpr Address c{uint64_t{2}};
    EXPECT_EQ(a, b);
    EXPECT_NE(a, c);
}

TEST(Address, ordering)
{
    constexpr Address a{uint64_t{1}};
    constexpr Address b{uint64_t{2}};
    EXPECT_LT(a, b);
    EXPECT_GT(b, a);
    EXPECT_LE(a, a);
    EXPECT_GE(b, b);
}

TEST(Address, ordering_lexicographic)
{
    // A value with a higher first byte should compare greater,
    // regardless of trailing bytes.
    constexpr Address high{uint8_t{0xFF}};
    constexpr Address low{uint64_t{UINT64_MAX}};
    EXPECT_GT(high, low);
}

// ---------------------------------------------------------------------------
// _address literal
// ---------------------------------------------------------------------------

TEST(Address, literal_parses_correctly)
{
    constexpr auto val = 0x0000000000000000000000000000000000000001_address;
    constexpr Address expected{uint64_t{1}};
    EXPECT_EQ(val, expected);
}

TEST(Address, literal_full_width)
{
    constexpr auto val = 0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_address;
    for (int i = 0; i < 20; i += 4) {
        EXPECT_EQ(val.bytes[i + 0], 0xDE);
        EXPECT_EQ(val.bytes[i + 1], 0xAD);
        EXPECT_EQ(val.bytes[i + 2], 0xBE);
        EXPECT_EQ(val.bytes[i + 3], 0xEF);
    }
}

// ---------------------------------------------------------------------------
// address_from_hex
// ---------------------------------------------------------------------------

TEST(Address, from_hex_without_prefix)
{
    auto const val =
        address_from_hex("0000000000000000000000000000000000000042");
    EXPECT_EQ(val.bytes[19], 0x42);
}

TEST(Address, from_hex_with_prefix)
{
    auto const val =
        address_from_hex("0x0000000000000000000000000000000000000042");
    EXPECT_EQ(val.bytes[19], 0x42);
}

// ---------------------------------------------------------------------------
// Well-known constants
// ---------------------------------------------------------------------------

TEST(Address, staking_ca_matches_uint64)
{
    constexpr Address staking{uint64_t{0x1000}};
    EXPECT_EQ(staking.bytes[18], 0x10);
    EXPECT_EQ(staking.bytes[19], 0x00);
}

// ---------------------------------------------------------------------------
// Hashing — std::hash, ankerl, boost
// ---------------------------------------------------------------------------

TEST(Address, std_hash_equal_values_same_hash)
{
    Address const a{uint64_t{42}};
    Address const b{uint64_t{42}};
    EXPECT_EQ(std::hash<Address>{}(a), std::hash<Address>{}(b));
}

TEST(Address, std_hash_distinguishes_in_unordered_set)
{
    Address const a{uint64_t{1}};
    Address const b{uint64_t{2}};

    std::unordered_set<Address> values;
    values.insert(a);
    values.insert(b);

    EXPECT_EQ(values.size(), 2);
    EXPECT_TRUE(values.contains(a));
    EXPECT_TRUE(values.contains(b));
}

TEST(Address, ankerl_hash_consistent_with_std)
{
    Address const val{uint64_t{123}};
    auto const std_h = std::hash<Address>{}(val);
    auto const ankerl_h = ankerl::unordered_dense::hash<Address>{}(val);
    EXPECT_EQ(std_h, ankerl_h);
}

TEST(Address, boost_hash_consistent_with_std)
{
    Address const val{uint64_t{456}};
    auto const std_h = std::hash<Address>{}(val);
    auto const boost_h = boost::hash_value(val);
    EXPECT_EQ(std_h, boost_h);
}

TEST(Address, usable_in_unordered_set)
{
    std::unordered_set<Address> set;
    set.insert(Address{uint64_t{1}});
    set.insert(Address{uint64_t{2}});
    set.insert(Address{uint64_t{1}});
    EXPECT_EQ(set.size(), 2);
}

// ---------------------------------------------------------------------------
// evmc_address implicit conversion
// ---------------------------------------------------------------------------

TEST(Address, implicit_from_evmc_address)
{
    evmc_address raw{};
    raw.bytes[19] = 0x07;
    Address const wrapped = raw;
    EXPECT_EQ(wrapped.bytes[19], 0x07);
}

// ---------------------------------------------------------------------------
// byte_string_view conversion
// ---------------------------------------------------------------------------

TEST(Address, converts_to_byte_string_view)
{
    Address const val{uint64_t{0xFF}};
    byte_string_view const view = val;
    EXPECT_EQ(view.size(), 20);
    EXPECT_EQ(view[19], 0xFF);
}

// ---------------------------------------------------------------------------
// is_zero
// ---------------------------------------------------------------------------

TEST(Address, is_zero_for_zero_address)
{
    constexpr Address zero;
    EXPECT_TRUE(is_zero(zero));
}

TEST(Address, is_zero_for_nonzero_address)
{
    constexpr Address nonzero{uint64_t{1}};
    EXPECT_FALSE(is_zero(nonzero));
}

// ---------------------------------------------------------------------------
// sizeof and alignof
// ---------------------------------------------------------------------------

TEST(Address, size_and_alignment)
{
    EXPECT_EQ(sizeof(Address), 20);
    EXPECT_EQ(alignof(Address), 1);
}

// ---------------------------------------------------------------------------
// Type traits — FFI safety
// ---------------------------------------------------------------------------

TEST(Address, standard_layout_and_trivially_copyable)
{
    EXPECT_TRUE(std::is_standard_layout_v<Address>);
    EXPECT_TRUE(std::is_trivially_copyable_v<Address>);
}

// ---------------------------------------------------------------------------
// evmc_address round-trip (base slicing)
// ---------------------------------------------------------------------------

TEST(Address, roundtrip_through_evmc_address)
{
    Address const original{uint64_t{0xDEADBEEF}};
    evmc_address const &base = original;
    Address const recovered{base};
    EXPECT_EQ(original, recovered);
}

// ---------------------------------------------------------------------------
// Variadic byte constructor boundary sizes
// ---------------------------------------------------------------------------

TEST(Address, variadic_byte_constructor_single_byte)
{
    constexpr Address val{uint8_t{0xFF}};
    EXPECT_EQ(val.bytes[0], 0xFF);
    for (int i = 1; i < 20; ++i) {
        EXPECT_EQ(val.bytes[i], 0) << "byte " << i;
    }
}

TEST(Address, variadic_byte_constructor_full_width)
{
    constexpr Address val{
        uint8_t{0x01}, uint8_t{0x02}, uint8_t{0x03}, uint8_t{0x04},
        uint8_t{0x05}, uint8_t{0x06}, uint8_t{0x07}, uint8_t{0x08},
        uint8_t{0x09}, uint8_t{0x0A}, uint8_t{0x0B}, uint8_t{0x0C},
        uint8_t{0x0D}, uint8_t{0x0E}, uint8_t{0x0F}, uint8_t{0x10},
        uint8_t{0x11}, uint8_t{0x12}, uint8_t{0x13}, uint8_t{0x14}};
    for (int i = 0; i < 20; ++i) {
        EXPECT_EQ(val.bytes[i], i + 1) << "byte " << i;
    }
}

// ---------------------------------------------------------------------------
// constexpr comparisons
// ---------------------------------------------------------------------------

TEST(Address, constexpr_equality_and_ordering)
{
    static_assert(Address{uint64_t{1}} == Address{uint64_t{1}});
    static_assert(Address{uint64_t{1}} != Address{uint64_t{2}});
    static_assert(Address{uint64_t{1}} < Address{uint64_t{2}});
    static_assert(Address{uint64_t{2}} > Address{uint64_t{1}});
}
