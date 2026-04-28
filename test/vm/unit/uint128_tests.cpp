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

#include <category/core/runtime/uint128.hpp>

#include <gtest/gtest.h>

#include <bit>
#include <compare>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>

using monad::uint128_t;
using monad::operator""_u128;

TEST(Uint128, equality)
{
    EXPECT_EQ(uint128_t(0, 0), uint128_t(0, 0));
    EXPECT_EQ(uint128_t(1, 0), uint128_t(1, 0));
    EXPECT_EQ(uint128_t(0, 1), uint128_t(0, 1));
    EXPECT_NE(uint128_t(0, 0), uint128_t(1, 0));
    EXPECT_NE(uint128_t(0, 0), uint128_t(0, 1));
    EXPECT_NE(uint128_t(1, 0), uint128_t(0, 1));
}

TEST(Uint128, ordering)
{
    // equal
    EXPECT_EQ(uint128_t(0, 0) <=> uint128_t(0, 0), std::strong_ordering::equal);

    // hi word dominates
    EXPECT_LT(uint128_t(0, 0), uint128_t(0, 1));
    EXPECT_GT(uint128_t(0, 1), uint128_t(0, 0));

    // lo word breaks tie when hi is equal
    EXPECT_LT(uint128_t(0, 1), uint128_t(1, 1));
    EXPECT_GT(uint128_t(1, 1), uint128_t(0, 1));

    // large lo does not outweigh small hi
    EXPECT_LT(
        uint128_t(std::numeric_limits<uint64_t>::max(), 0), uint128_t(0, 1));
    EXPECT_GT(
        uint128_t(0, 1), uint128_t(std::numeric_limits<uint64_t>::max(), 0));

    // UINT128_MAX is greater than everything else
    EXPECT_GT(
        (uint128_t(
            std::numeric_limits<uint64_t>::max(),
            std::numeric_limits<uint64_t>::max())),
        uint128_t(std::numeric_limits<uint64_t>::max(), 0));
    EXPECT_GT(
        (uint128_t(
            std::numeric_limits<uint64_t>::max(),
            std::numeric_limits<uint64_t>::max())),
        uint128_t(0, std::numeric_limits<uint64_t>::max()));
}

namespace
{
    // Verify compile-time division takes the consteval path.
    static_assert(uint128_t{6, 0} / uint64_t{3} == uint128_t{2, 0});
    static_assert(uint128_t{0, 6} / uint64_t{3} == uint128_t{0, 2});
} // namespace

TEST(Uint128, division_lo_only)
{
    // Divisor larger than hi word (q_hi == 0), single effective div.
    EXPECT_EQ(uint128_t(6, 0) / uint64_t{3}, uint128_t(2, 0));
    EXPECT_EQ(uint128_t(7, 0) / uint64_t{3}, uint128_t(2, 0)); // truncates
    EXPECT_EQ(uint128_t(0, 0) / uint64_t{1}, uint128_t(0, 0));
    EXPECT_EQ(uint128_t(UINT64_MAX, 0) / uint64_t{1}, uint128_t(UINT64_MAX, 0));
}

TEST(Uint128, division_hi_word)
{
    // hi >= b, so q_hi > 0 — exercises the two-divq path.
    // value = 6 * 2^64, result = 2 * 2^64 = {0, 2}
    EXPECT_EQ(uint128_t(0, 6) / uint64_t{3}, uint128_t(0, 2));
    // value = 3 * 2^64, result = 2^63 * 3 = {0, 1} remainder 2^64/2
    // 3 * 2^64 / 2 = 1 * 2^64 + 2^63 = {2^63, 1}
    EXPECT_EQ(uint128_t(0, 3) / uint64_t{2}, uint128_t(uint64_t{1} << 63, 1));
    // divide by 1 — identity
    EXPECT_EQ(uint128_t(42, 7) / uint64_t{1}, uint128_t(42, 7));
}

TEST(Uint128, division_max)
{
    constexpr uint64_t u64max = std::numeric_limits<uint64_t>::max();
    // UINT128_MAX / UINT64_MAX == 2^64 + 1 == {1, 1}
    // because (2^64-1)(2^64+1) == 2^128 - 1
    EXPECT_EQ(uint128_t(u64max, u64max) / u64max, uint128_t(1, 1));
    // UINT128_MAX / 1 == UINT128_MAX
    EXPECT_EQ(
        uint128_t(u64max, u64max) / uint64_t{1}, uint128_t(u64max, u64max));
}

TEST(Uint128, division_de_safety)
{
    // r_hi = a.hi % b is always < b, so the 128-bit hardware divq quotient
    // always fits in 64 bits (#DE-safe). Test at the boundary r_hi = b-1,
    // which maximises the numerator fed to the second divq step.
    constexpr uint64_t u64max = std::numeric_limits<uint64_t>::max();

    // b=2, a.hi=1 → r_hi=1=b-1; value=2^65-1, quotient=UINT64_MAX
    EXPECT_EQ(uint128_t(u64max, 1) / uint64_t{2}, uint128_t(u64max, 0));
    // b=3, a.hi=2 → r_hi=2=b-1; value=3*2^64-1, quotient=UINT64_MAX
    EXPECT_EQ(uint128_t(u64max, 2) / uint64_t{3}, uint128_t(u64max, 0));
    // b=UINT64_MAX, a.hi=UINT64_MAX-1 → r_hi=UINT64_MAX-1=b-1
    EXPECT_EQ(uint128_t(u64max, u64max - 1) / u64max, uint128_t(u64max, 0));
}

TEST(Uint128, bitwise_not)
{
    EXPECT_EQ(~uint128_t(0, 0), uint128_t(UINT64_MAX, UINT64_MAX));
    EXPECT_EQ(~uint128_t(UINT64_MAX, UINT64_MAX), uint128_t(0, 0));
    // ~lo and ~hi are independent
    EXPECT_EQ(~uint128_t(0, UINT64_MAX), uint128_t(UINT64_MAX, 0));
    EXPECT_EQ(~uint128_t(UINT64_MAX, 0), uint128_t(0, UINT64_MAX));
    // double-not is identity
    EXPECT_EQ(~~uint128_t(0xdeadbeef, 0xcafe), uint128_t(0xdeadbeef, 0xcafe));
}

TEST(Uint128, multiply_basic)
{
    EXPECT_EQ(uint128_t(0, 0) * uint128_t(0, 0), uint128_t(0, 0));
    EXPECT_EQ(uint128_t(1, 0) * uint128_t(1, 0), uint128_t(1, 0));
    EXPECT_EQ(uint128_t(6, 0) * uint128_t(7, 0), uint128_t(42, 0));
    // 2^64 * 2^64 = 2^128 overflows to 0 (wrapping)
    EXPECT_EQ(uint128_t(0, 1) * uint128_t(0, 1), uint128_t(0, 0));
    // 2 * 2^64 = 2^65 = {0, 2}
    EXPECT_EQ(uint128_t(2, 0) * uint128_t(0, 1), uint128_t(0, 2));
}

TEST(Uint128, multiply_overflow_wraps)
{
    constexpr uint64_t u64max = std::numeric_limits<uint64_t>::max();
    // UINT128_MAX * 2: (2^128 - 1) * 2 mod 2^128 = 2^128 - 2 = {u64max-1,
    // u64max}
    EXPECT_EQ(
        uint128_t(u64max, u64max) * uint128_t(2, 0),
        uint128_t(u64max - 1, u64max));
    // UINT128_MAX * UINT128_MAX: (2^128 - 1)^2 mod 2^128 = 1
    EXPECT_EQ(
        uint128_t(u64max, u64max) * uint128_t(u64max, u64max), uint128_t(1, 0));
}

TEST(Uint128, right_shift)
{
    // shift by 0 — identity
    EXPECT_EQ(uint128_t(0xf, 0xa) >> 0, uint128_t(0xf, 0xa));

    // shift within lo word (shift < 64)
    EXPECT_EQ(uint128_t(0x10, 0) >> 4, uint128_t(0x01, 0));

    // shift by exactly 63: hi bit 0 moves into lo bit 63
    EXPECT_EQ(uint128_t(0, 2) >> 63, uint128_t(4, 0));

    // shift by exactly 64: lo = hi, hi = 0
    EXPECT_EQ(uint128_t(0, 0xdeadbeef) >> 64, uint128_t(0xdeadbeef, 0));

    // shift by 65: one further right than >>64
    EXPECT_EQ(uint128_t(0, 4) >> 65, uint128_t(2, 0));

    // shift by 127: only bit 127 (hi bit 63) survives
    EXPECT_EQ(uint128_t(0, uint64_t{1} << 63) >> 127, uint128_t(1, 0));
    // bit 64 shifted right 127 lands at bit -63 — gone
    EXPECT_EQ(uint128_t(0, 1) >> 127, uint128_t(0, 0));

    // UINT128_MAX >> 1 = {UINT64_MAX, UINT64_MAX >> 1}
    EXPECT_EQ(
        uint128_t(UINT64_MAX, UINT64_MAX) >> 1,
        uint128_t(UINT64_MAX, UINT64_MAX >> 1));
}

TEST(Uint128, byteswap)
{
    EXPECT_EQ(byteswap(uint128_t(0, 0)), uint128_t(0, 0));
    // lo bytes reversed become hi, vice versa
    EXPECT_EQ(
        byteswap(uint128_t(0x0102030405060708ULL, 0)),
        uint128_t(0, 0x0807060504030201ULL));
    // double byteswap is identity
    EXPECT_EQ(
        byteswap(
            byteswap(uint128_t(0xdeadbeefcafe0123ULL, 0xabcdef9876543210ULL))),
        uint128_t(0xdeadbeefcafe0123ULL, 0xabcdef9876543210ULL));
    // lo and hi are each individually byteswapped then swapped with each other
    EXPECT_EQ(
        byteswap(uint128_t(1, 2)),
        uint128_t(std::byteswap(uint64_t{2}), std::byteswap(uint64_t{1})));
}

TEST(Uint128, to_string_decimal)
{
    EXPECT_EQ(to_string(uint128_t(0, 0)), "0");
    EXPECT_EQ(to_string(uint128_t(1, 0)), "1");
    EXPECT_EQ(to_string(uint128_t(42, 0)), "42");
    EXPECT_EQ(to_string(uint128_t(UINT64_MAX, 0)), "18446744073709551615");
    // 2^64
    EXPECT_EQ(to_string(uint128_t(0, 1)), "18446744073709551616");
    // UINT128_MAX
    EXPECT_EQ(
        to_string(uint128_t(UINT64_MAX, UINT64_MAX)),
        "340282366920938463463374607431768211455");
}

TEST(Uint128, to_string_hex)
{
    EXPECT_EQ(to_string(uint128_t(0, 0), 16), "0");
    EXPECT_EQ(to_string(uint128_t(0xff, 0), 16), "ff");
    EXPECT_EQ(to_string(uint128_t(0, 1), 16), "10000000000000000");
    EXPECT_EQ(
        to_string(uint128_t(UINT64_MAX, UINT64_MAX), 16),
        "ffffffffffffffffffffffffffffffff");
}

TEST(Uint128, to_string_binary)
{
    EXPECT_EQ(to_string(uint128_t(0b101, 0), 2), "101");
    // 2^64 in binary: 1 followed by 64 zeros
    EXPECT_EQ(to_string(uint128_t(0, 1), 2), "1" + std::string(64, '0'));
}

TEST(Uint128, from_string_decimal)
{
    EXPECT_EQ(uint128_t::from_string("0"), uint128_t(0, 0));
    EXPECT_EQ(uint128_t::from_string("1"), uint128_t(1, 0));
    EXPECT_EQ(uint128_t::from_string("42"), uint128_t(42, 0));
    // 2^64
    EXPECT_EQ(uint128_t::from_string("18446744073709551616"), uint128_t(0, 1));
    // UINT128_MAX
    EXPECT_EQ(
        uint128_t::from_string("340282366920938463463374607431768211455"),
        uint128_t(UINT64_MAX, UINT64_MAX));
}

TEST(Uint128, from_string_hex)
{
    EXPECT_EQ(uint128_t::from_string("0x0"), uint128_t(0, 0));
    EXPECT_EQ(uint128_t::from_string("0x1"), uint128_t(1, 0));
    EXPECT_EQ(uint128_t::from_string("0xff"), uint128_t(0xff, 0));
    EXPECT_EQ(uint128_t::from_string("0xFF"), uint128_t(0xff, 0));
    // 2^64
    EXPECT_EQ(uint128_t::from_string("0x10000000000000000"), uint128_t(0, 1));
    // UINT128_MAX
    EXPECT_EQ(
        uint128_t::from_string("0xffffffffffffffffffffffffffffffff"),
        uint128_t(UINT64_MAX, UINT64_MAX));
}

TEST(Uint128, from_string_invalid)
{
    auto throws_invalid = [](char const *s) {
        EXPECT_THROW((void)uint128_t::from_string(s), std::invalid_argument)
            << "expected invalid_argument for: " << s;
    };
    auto throws_range = [](char const *s) {
        EXPECT_THROW((void)uint128_t::from_string(s), std::out_of_range)
            << "expected out_of_range for: " << s;
    };

    throws_invalid(""); // empty
    throws_invalid("0x"); // hex prefix with no digits
    throws_invalid("12x4"); // non-digit in decimal
    throws_invalid("0x1g"); // non-hex digit
    // UINT128_MAX + 1 in decimal
    throws_range("340282366920938463463374607431768211456");
    // 33 hex digits — one too many
    throws_range("0x1ffffffffffffffffffffffffffffffff");
}

TEST(Uint128, udl)
{
    EXPECT_EQ(0_u128, uint128_t(0, 0));
    EXPECT_EQ(42_u128, uint128_t(42, 0));
    EXPECT_EQ(0xff_u128, uint128_t(0xff, 0));
    // 2^64
    EXPECT_EQ(18446744073709551616_u128, uint128_t(0, 1));
    // UINT128_MAX
    EXPECT_EQ(
        340282366920938463463374607431768211455_u128,
        uint128_t(UINT64_MAX, UINT64_MAX));
}

TEST(Uint128, numeric_limits)
{
    using lim = std::numeric_limits<uint128_t>;
    static_assert(lim::is_specialized);
    static_assert(lim::is_integer);
    static_assert(!lim::is_signed);
    static_assert(lim::is_modulo);
    static_assert(lim::digits == 128);
    EXPECT_EQ(lim::min(), uint128_t(0, 0));
    EXPECT_EQ(lim::max(), uint128_t(UINT64_MAX, UINT64_MAX));
    EXPECT_EQ(lim::lowest(), uint128_t(0, 0));
}
