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

#include <category/vm/runtime/uint256.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <string>
#include <sys/types.h>
#include <tuple>
#include <vector>

using namespace monad::vm::runtime;

static_assert(
    alignof(uint256_t) == alignof(::intx::uint256),
    "Alignment of uint256_t is incompatible with intx");
static_assert(
    sizeof(uint256_t) == sizeof(::intx::uint256),
    "Size of uint256_t is incompatible with intx");

TEST(uint256, signextend)
{
    uint256_t i;
    uint256_t x;

    i = 0;
    x = 0xff8000;
    ASSERT_EQ(signextend(i, x), 0);

    i = 1;
    x = 0xff8000;
    ASSERT_EQ(signextend(i, x), ~uint256_t{0xffff} | x);

    i = 2;
    x = 0xff8000;
    ASSERT_EQ(signextend(i, x), ~uint256_t{0xffffff} | x);

    i = 3;
    x = 0xff8000;
    ASSERT_EQ(signextend(i, x), x);

    i = 30;
    x = uint256_t{0x0080} << 240;
    ASSERT_EQ(signextend(i, x), uint256_t{0xff80} << 240);

    i = 30;
    x = uint256_t{0x0070} << 240;
    ASSERT_EQ(signextend(i, x), uint256_t{0x0070} << 240);

    i = 31;
    x = uint256_t{0xf0} << 248;
    ASSERT_EQ(signextend(i, x), uint256_t{0xf0} << 248);
}

TEST(uint256, byte)
{
    uint256_t i;
    uint256_t x;

    i = 31;
    x = 0xff8000;
    ASSERT_EQ(byte(i, x), 0);

    i = 30;
    x = 0xff8000;
    ASSERT_EQ(byte(i, x), 0x80);

    i = 29;
    x = 0xff8000;
    ASSERT_EQ(byte(i, x), 0xff);

    i = 28;
    x = 0xff8000;
    ASSERT_EQ(byte(i, x), 0);

    i = 1;
    x = uint256_t{0x0080} << 240;
    ASSERT_EQ(byte(i, x), 0x80);

    i = 0;
    x = uint256_t{0x0080} << 240;
    ASSERT_EQ(byte(i, x), 0);

    i = 0;
    x = uint256_t{0xf0} << 248;
    ASSERT_EQ(byte(i, x), 0xf0);

    i = 32;
    x = uint256_t{0xff} << 248;
    ASSERT_EQ(byte(i, x), 0);
}

TEST(uint256, sar)
{
    uint256_t i;
    uint256_t x;

    i = 0;
    x = uint256_t{0x80} << 248;
    ASSERT_EQ(sar(i, x), x);

    i = 1;
    x = uint256_t{0x80} << 248;
    ASSERT_EQ(sar(i, x), uint256_t{0xc0} << 248);

    i = 1;
    x = uint256_t{0x70} << 248;
    ASSERT_EQ(sar(i, x), uint256_t{0x38} << 248);

    i = 255;
    x = uint256_t{0x80} << 248;
    ASSERT_EQ(sar(i, x), ~uint256_t{0});

    i = 254;
    x = uint256_t{0x80} << 248;
    ASSERT_EQ(sar(i, x), ~uint256_t{0} - 1);

    i = 254;
    x = uint256_t{0x40} << 248;
    ASSERT_EQ(sar(i, x), 1);

    i = 255;
    x = uint256_t{0x7f} << 248;
    ASSERT_EQ(sar(i, x), 0);
}

template <size_t N>
void test_bit_width()
{
    ASSERT_EQ(bit_width(pow2(N)), N + 1);
    if constexpr (N > 0) {
        test_bit_width<N - 1>();
    }
}

TEST(uint256, bit_width)
{
    test_bit_width<255>();
}

::intx::uint256 from_words(std::array<uint64_t, 4> words)
{
    return ::intx::uint256{words[0], words[1], words[2], words[3]};
}

uint256_t from_intx(::intx::uint256 const &x)
{
    return uint256_t{x[0], x[1], x[2], x[3]};
}

::intx::uint256 to_intx(uint256_t const &x)
{
    return ::intx::uint256{x[0], x[1], x[2], x[3]};
}

TEST(uint256, intx_iso)
{
    uint64_t ONES = ~uint64_t(0);
    std::array<uint64_t, 4> const inputs[]{
        {0, 0, 0, 0},
        {1, 0, 0, 0},
        {0, 1, 0, 0},
        {0, 0, 1, 0},
        {0, 0, 0, 1},
        {ONES, ONES, ONES, ONES},
        {ONES, 0, 0, 0},
        {0, ONES, 0, 0},
        {0, 0, ONES, 0},
        {0, 0, 0, ONES},
        {0x12345678, 0x9abcdef0, 0x87654321, 0x0fedcba9}};

    for (auto input : inputs) {
        auto x = uint256_t{input};
        auto intx = from_words(input);
        ASSERT_EQ(to_intx(x), intx);
        ASSERT_EQ(x, from_intx(intx));
    }
}

TEST(uint256, avx_iso)
{
    uint64_t ones = ~uint64_t(0);
    std::vector<uint256_t> const inputs{
        {0, 0, 0, 0},
        {1, 0, 0, 0},
        {0, 1, 0, 0},
        {0, 0, 1, 0},
        {0, 0, 0, 1},
        {ones, ones, ones, ones},
        {ones, 0, 0, 0},
        {0, ones, 0, 0},
        {0, 0, ones, 0},
        {0, 0, 0, ones},
        {0x12345678, 0x9abcdef0, 0x87654321, 0x0fedcba9}};

    for (auto input : inputs) {
        ASSERT_EQ(input, uint256_t(input.to_avx()));
    }
}

TEST(uint256, constructors)
{
    uint256_t x;
    ::intx::uint256 intx;

    x = uint256_t();
    intx = 0;
    ASSERT_EQ(to_intx(x), intx);

    x = 1;
    intx = 1;
    ASSERT_EQ(to_intx(x), intx);

    x = 0xabcd;
    intx = 0xabcd;
    ASSERT_EQ(to_intx(x), intx);

    x = {0xabcd, 0x1234};
    intx = {0xabcd, 0x1234};
    ASSERT_EQ(to_intx(x), intx);

    x = {0xabcd, 0x1234, 0xdcba};
    intx = {0xabcd, 0x1234, 0xdcba};
    ASSERT_EQ(to_intx(x), intx);

    x = {0xabcd, 0x1234, 0xdcba, 0x4321};
    intx = {0xabcd, 0x1234, 0xdcba, 0x4321};
    ASSERT_EQ(to_intx(x), intx);

    x = -1;
    intx = -1;
    ASSERT_EQ(to_intx(x), intx);

    x = {0xabcd, -0x1234, 0xdcba, -0x4321};
    intx = {0xabcd, -0x1234, 0xdcba, -0x4321};
    ASSERT_EQ(to_intx(x), intx);
}

TEST(uint256, literals)
{
    uint256_t x;

    x = 0_u256;
    ASSERT_EQ(x, uint256_t(0, 0, 0, 0));

    x = 1_u256;
    ASSERT_EQ(x, uint256_t(1, 0, 0, 0));

    x = 0xff_u256;
    ASSERT_EQ(x, uint256_t(0xff, 0, 0, 0));

    x = 0x4a4b4c4d414243443a3b3c3d313233342a2b2c2d212223241a1b1c1d11121314_u256;
    ASSERT_EQ(
        x,
        uint256_t(
            0x1a1b1c1d11121314,
            0x2a2b2c2d21222324,
            0x3a3b3c3d31323334,
            0x4a4b4c4d41424344));
}

TEST(uint256, index)
{
    uint256_t x = {1, 2, 3, 4};

    ASSERT_EQ(x[0], 1);
    ASSERT_EQ(x[1], 2);
    ASSERT_EQ(x[2], 3);
    ASSERT_EQ(x[3], 4);
}

TEST(uint256, bool_cast)
{
    for (size_t i = 0; i < 4; ++i) {
        uint256_t x = 0;
        ASSERT_EQ(static_cast<bool>(x), false);
        x[i] = 1;
        ASSERT_EQ(static_cast<bool>(x), true);
        x = 0;
        ASSERT_EQ(static_cast<bool>(x), false);
        x[i] = uint64_t{1} << 63;
        ASSERT_EQ(static_cast<bool>(x), true);
    }
}

TEST(uint256, int_cast)
{
    uint256_t x = {0xabcd, 0xdef0, 0x1234, 0x5678};
    ASSERT_EQ(static_cast<uint64_t>(x), 0xabcd);
    ASSERT_EQ(static_cast<int64_t>(x), 0xabcd);
    ASSERT_EQ(static_cast<uint32_t>(x), 0xabcd);
    ASSERT_EQ(static_cast<int32_t>(x), 0xabcd);

    x = {-0xabcd, 0xdef0, 0x1234, 0x5678};
    ASSERT_EQ(static_cast<uint64_t>(x), -0xabcd);
    ASSERT_EQ(static_cast<int64_t>(x), -0xabcd);
    ASSERT_EQ(static_cast<uint32_t>(x), -0xabcd);
    ASSERT_EQ(static_cast<int32_t>(x), -0xabcd);

    x = {0x1234aabbccdd4321, 0xdef0, 0x1234, 0x5678};
    ASSERT_EQ(static_cast<uint64_t>(x), 0x1234aabbccdd4321);
    ASSERT_EQ(static_cast<int64_t>(x), 0x1234aabbccdd4321);
    ASSERT_EQ(static_cast<uint32_t>(x), 0xccdd4321);
    ASSERT_EQ(static_cast<int32_t>(x), 0xccdd4321);
    ASSERT_EQ(static_cast<uint16_t>(x), 0x4321);
    ASSERT_EQ(static_cast<int16_t>(x), 0x4321);
    ASSERT_EQ(static_cast<uint8_t>(x), 0x21);
    ASSERT_EQ(static_cast<int8_t>(x), 0x21);
}

TEST(uint256, constexpr_fallbacks)
{
    uint64_t const inputs[] = {
        0,
        1,
        static_cast<uint64_t>(std::numeric_limits<int64_t>::max()),
        static_cast<uint64_t>(std::numeric_limits<int64_t>::min()),
        0xc411987422d1b087,
        0x3b99b4f6c7da07b2,
        0x26ff29d37306530f,
        0x6c955311f20d471c,
        0x71668f0478f99486,
        0x37809cb69732cdb7,
        0xf66eb4528f6aadff,
        0xd3e0839d43dcc0bc,
        0x0008a54508aaf378,
        0x7cc2c8466df30bd5,

    };
    for (auto x : inputs) {
        for (auto y : inputs) {
            for (auto c : {true, false}) {
                ASSERT_EQ(addc_constexpr(x, y, c), addc_intrinsic(x, y, c));
                ASSERT_EQ(subb_constexpr(x, y, c), subb_intrinsic(x, y, c));
            }
            for (size_t shift = 0; shift < 64; shift++) {
                auto shift_8 = static_cast<uint8_t>(shift);
                ASSERT_EQ(
                    shld_constexpr(x, y, shift_8),
                    shld_intrinsic(x, y, shift_8));
                ASSERT_EQ(
                    shrd_constexpr(x, y, shift_8),
                    shrd_intrinsic(x, y, shift_8));
            }
            for (auto v : inputs) {
                if (x >= v || v == 0) {
                    continue;
                }
                ASSERT_EQ(div_constexpr(x, y, v), div_intrinsic(x, y, v));
            }
        }
    }
}

constexpr uint256_t test_inputs[] = {
    {0, 0, 0, 0},
    {1, 0, 0, 0},
    {0, 1, 0, 0},
    {0, 0, 1, 0},
    {0, 0, 0, 1},
    {~0, 0, 0, 0},
    {0, ~0, 0, 0},
    {0, 0, ~0, 0},
    {0, 0, 0, ~0},
    {~0, ~0, ~0, ~0},
    {~0, ~0, ~0, 0x07ffffffffffffff},
    {0xff, 0, 0, 0},
    {0, 0xff, 0, 0},
    {0, 0, 0xff, 0},
    {0, 0, 0, 0xff},
    {0x40, 0, 0, 0},
    {0, 0x40, 0, 0},
    {0, 0, 0x40, 0},
    {0, 0, 0, 0x40},
    {0x1234, 0, 0, 0},
    {0, 0x1234, 0, 0},
    {0, 0, 0x1234, 0},
    {0, 0, 0, 0x1234},
    {0x1234, 0xabcd, 0xbcda, 0x4321},
    {
        0xabcda1b2c3d41234,
        0x12341a2b3c4dabcd,
        0xdcbad4c3b2a14321,
        0x43214d3c2b1abcda,
    },
    {
        0x43214d3c2b1abcda,
        0xabcda1b2c3d41234,
        0x12341a2b3c4dabcd,
        0xdcbad4c3b2a14321,
    },
    {
        0xdcbad4c3b2a14321,
        0x43214d3c2b1abcda,
        0xabcda1b2c3d41234,
        0x12341a2b3c4dabcd,
    },
    {
        0x12341a2b3c4dabcd,
        0xdcbad4c3b2a14321,
        0x43214d3c2b1abcda,
        0xabcda1b2c3d41234,
    },
};

TEST(uint256, arithmetic)
{
    for (auto const &x : test_inputs) {
        for (auto const &y : test_inputs) {
            ASSERT_EQ(x + y, from_intx(to_intx(x) + to_intx(y)));
            ASSERT_EQ(x - y, from_intx(to_intx(x) - to_intx(y)));
            ASSERT_EQ(x * y, from_intx(to_intx(x) * to_intx(y)));
            ASSERT_EQ(
                exp(x, y), from_intx(::intx::exp(to_intx(x), to_intx(y))));

            if (y != 0) {
                auto const q = x / y;
                auto const r = x % y;
                ASSERT_LT(r, y);
                ASSERT_EQ(q * y + r, x);

                auto const [sq, sr] = sdivrem(x, y);
                auto [sqx, srx] = ::intx::sdivrem(to_intx(x), to_intx(y));
                ASSERT_EQ(sq, from_intx(sqx));
                ASSERT_EQ(sr, from_intx(srx));
            }

            for (auto const &z : test_inputs) {
                if (z == 0) {
                    continue;
                }
                ASSERT_EQ(
                    addmod(x, y, z),
                    from_intx(
                        ::intx::addmod(to_intx(x), to_intx(y), to_intx(z))));
                ASSERT_EQ(
                    mulmod(x, y, z),
                    from_intx(
                        ::intx::mulmod(to_intx(x), to_intx(y), to_intx(z))));
            }
        }
        ASSERT_EQ(-x, from_intx(-(to_intx(x))));
    }
}

template <size_t R, size_t M, size_t N>
void check_truncating_mul(
    words_t<M> const &x, words_t<N> const &y,
    words_t<M + N> const &full) noexcept
{
    auto const prod_rt = truncating_mul_runtime<R>(x, y);
    auto const prod_ce = truncating_mul_constexpr<R>(x, y);
    for (size_t i = 0; i < R; i++) {
        ASSERT_EQ(prod_rt[i], full[i]);
        ASSERT_EQ(prod_ce[i], full[i]);
    }
}

template <size_t M, size_t N>
constexpr words_t<M + N>
intx_umul_words(words_t<M> const &x, words_t<N> const &y) noexcept
{
    auto const x_intx = std::bit_cast<::intx::uint<M * 64>>(x);
    auto const y_intx = std::bit_cast<::intx::uint<N * 64>>(y);
    return std::bit_cast<words_t<M + N>>(::intx::umul(x_intx, y_intx));
}

TEST(uint256, multiplication)
{
    // 1-word x 1-word
    constexpr uint64_t single_word_inputs[]{
        0UL,
        1UL,
        static_cast<uint64_t>(std::numeric_limits<int64_t>::max()),
        static_cast<uint64_t>(std::numeric_limits<int64_t>::min()),
        0xff,
        0xabcda1b2c3d41234};
    for (auto const &x : single_word_inputs) {
        for (auto const &y : single_word_inputs) {
            auto const product_u128 = static_cast<uint128_t>(x) * y;
            words_t<2> product{
                static_cast<uint64_t>(product_u128),
                static_cast<uint64_t>(product_u128 >> 64)};
            check_truncating_mul<1, 1, 1>({x}, {y}, product);
            check_truncating_mul<2, 1, 1>({x}, {y}, product);
        }
    }
    // 2-word x 1-word
    std::vector<std::array<uint64_t, 2>> two_word_inputs;
    for (auto const &w0 : single_word_inputs) {
        for (auto const &w1 : single_word_inputs) {
            two_word_inputs.push_back(std::array<uint64_t, 2>{w0, w1});
        }
    }
    for (auto const &x : two_word_inputs) {
        for (auto const &y0 : single_word_inputs) {
            // intx does not allow 64-bit numbers, we have to zero-extend y
            words_t<2> const y{y0, 0UL};
            auto const intx_product = intx_umul_words(x, y);
            ASSERT_EQ(intx_product[3], 0UL);

            check_truncating_mul<1>(x, y, intx_product);
            check_truncating_mul<2>(x, y, intx_product);
            check_truncating_mul<3>(x, y, intx_product);

            check_truncating_mul<1>(y, x, intx_product);
            check_truncating_mul<2>(y, x, intx_product);
            check_truncating_mul<3>(y, x, intx_product);
        }
    }
    // 2-word x 2-word
    for (auto const &x : two_word_inputs) {
        for (auto const &y : two_word_inputs) {
            auto const intx_product = intx_umul_words(x, y);

            check_truncating_mul<1>(x, y, intx_product);
            check_truncating_mul<2>(x, y, intx_product);
            check_truncating_mul<3>(x, y, intx_product);
            check_truncating_mul<4>(x, y, intx_product);

            check_truncating_mul<1>(y, x, intx_product);
            check_truncating_mul<2>(y, x, intx_product);
            check_truncating_mul<3>(y, x, intx_product);
            check_truncating_mul<4>(y, x, intx_product);
        }
    }
    // 4-word x 4-word
    for (auto const &xi : test_inputs) {
        for (auto const &yi : test_inputs) {
            auto x = xi.as_words();
            auto y = yi.as_words();

            auto const intx_product = intx_umul_words(x, y);

            check_truncating_mul<1>(x, y, intx_product);
            check_truncating_mul<2>(x, y, intx_product);
            check_truncating_mul<3>(x, y, intx_product);
            check_truncating_mul<4>(x, y, intx_product);
            check_truncating_mul<5>(x, y, intx_product);
            check_truncating_mul<6>(x, y, intx_product);
            check_truncating_mul<7>(x, y, intx_product);
            check_truncating_mul<8>(x, y, intx_product);
        }
    }
}

TEST(uint256, division)
{
    // Specific tests: inputs to cover special cases
    constexpr std::pair<uint256_t, uint256_t> div_inputs[]{
        {
            {0x00, 0xffffffffffffffff, 0xff, 0x00},
            {0xff, 0xffffffffffffffff, 0xff, 0x00},
        },
        {
            {0xff, 0xff, 0xff, 0xff},
            {0x00, 0xff00000000000000},
        },
        {
            {0xff, 0x00, 0x00, 0x00},
            {0xff, 0xff, 0x00, 0x00},
        },
        {
            {0xff, 0x00, 0x00, 0x00},
            {0xff, 0x00, 0x00, 0x00},
        },
        {
            {0xff, 0xff, 0xff, 0xff},
            {0xff, 0x00, 0x00, 0x00},
        },
        {
            {0xff, 0xff, 0xff, 0x00},
            {0xff, 0xff, 0x00, 0x00},

        },
        {
            {0x00, 0x00, 0x00, 0xff},
            {0x00, 0xff, 0xff, 0x00},

        },
        {
            {0x00, 0x00, 0xff, 0xff},
            {0x00, 0xff00, 0x00, 0x00},

        },
        {
            {0x00, 0x00, 0x00, 0xff},
            {0xff, 0x00, 0xff, 0x00},

        },
        {
            {0x00, 0x00, 0x00, 0xff},
            {0xff, 0x00, 0xff, 0x00},

        },
        {
            {0x0, 0x0, 0x0, 0x1},
            {0x100, 0x1, 0x1, 0x0},

        },
        {
            {0x0, 0x0, 0x1, 0x1},
            {0x1, 0x1, 0x1, 0x0},

        },
        {
            {0x00, 0x00, 0x00, 0xff},
            {0xff, 0x00, 0x00, 0x00},

        },
        {
            {0x00ff, 0x00, 0x00, 0xff},
            {0xff00, 0x00, 0x00, 0x00},
        },
        {
            {0x0, 0x0, 0x0, std::numeric_limits<uint64_t>::max()},
            {uint64_t{1} << 63, 1, 1, 0x0},
        }};
    for (auto const &[x, y] : div_inputs) {
        auto const [q, r] = udivrem(x, y);
        ASSERT_EQ(q * y + r, x);
        ASSERT_LT(r, y);
    }
}

TEST(uint256, predicates)
{
    for (auto const &x : test_inputs) {
        for (auto const &y : test_inputs) {
            ASSERT_EQ(x == y, to_intx(x) == to_intx(y));
            ASSERT_EQ(x < y, to_intx(x) < to_intx(y));
            ASSERT_EQ(x <= y, to_intx(x) <= to_intx(y));
            ASSERT_EQ(x > y, to_intx(x) > to_intx(y));
            ASSERT_EQ(x >= y, to_intx(x) >= to_intx(y));
            ASSERT_EQ(slt(x, y), ::intx::slt(to_intx(x), to_intx(y)));
        }
    }
}

TEST(uint256, bitwise)
{
    for (auto const &x : test_inputs) {
        for (auto const &y : test_inputs) {
            ASSERT_EQ(x | y, from_intx(to_intx(x) | to_intx(y)));
            ASSERT_EQ(x & y, from_intx(to_intx(x) & to_intx(y)));
            ASSERT_EQ(x ^ y, from_intx(to_intx(x) ^ to_intx(y)));
        }
        ASSERT_EQ(~x, from_intx(~(to_intx(x))));
    }
}

TEST(uint256, shifts)
{
    for (auto const &x : test_inputs) {
        for (uint64_t shift = 0; shift <= 256; shift++) {
            auto shl = x << shift;
            ASSERT_EQ(shl, from_intx(to_intx(x) << shift));

            auto shr = x >> shift;
            ASSERT_EQ(shr, from_intx(to_intx(x) >> shift));
        }
        for (auto const &y : test_inputs) {
            ASSERT_EQ(x << y, from_intx(to_intx(x) << to_intx(y)));
            ASSERT_EQ(x >> y, from_intx(to_intx(x) >> to_intx(y)));
        }
    }
}

TEST(uint256, load_store)
{
    for (auto x : test_inputs) {
        auto *le_bytes = std::bit_cast<uint8_t(*)[32]>(x.as_bytes());
        ASSERT_EQ(x, uint256_t::load_le_unsafe(x.as_bytes()));
        ASSERT_EQ(x, uint256_t::load_le(*le_bytes));

        uint8_t le_stored[32];
        x.store_le(le_stored);
        ASSERT_EQ(0, std::memcmp(le_bytes, le_stored, 32));
        ASSERT_EQ(x, uint256_t::load_le(le_stored));

        auto x_be = uint256_t{
            std::byteswap(x[3]),
            std::byteswap(x[2]),
            std::byteswap(x[1]),
            std::byteswap(x[0])};

        auto *be_bytes = std::bit_cast<uint8_t(*)[32]>(x_be.as_bytes());
        ASSERT_EQ(x, uint256_t::load_be_unsafe(x_be.as_bytes()));
        ASSERT_EQ(x, uint256_t::load_be(*be_bytes));

        uint8_t be_stored[32];
        x.store_be(be_stored);
        ASSERT_EQ(0, std::memcmp(be_bytes, be_stored, 32));
        ASSERT_EQ(x, uint256_t::load_be(be_stored));
    }
}

TEST(uint256, string_conversion)
{
    for (auto x : test_inputs) {
        ASSERT_EQ(x, uint256_t::from_string(x.to_string()));
        ASSERT_EQ(x, uint256_t::from_string("0x" + x.to_string(16)));
    }

    std::tuple<uint256_t, std::string, std::string> const test_cases[] = {
        {uint256_t{0}, "0", "0"},
        {uint256_t{1}, "1", "1"},
        {uint256_t{10}, "10", "a"},
        {uint256_t{0xff}, "255", "ff"},
        {uint256_t{
             0x8b1220bf20e9c14dUL,
             0x1c18c2c94b09b7dbUL,
             0xca70cd12f26ebc65UL,
             0xd6835e065763db1bUL},
         "970270554974245014818020843390850589381796664120294801326746575421176"
         "12175693",
         "d6835e065763db1bca70cd12f26ebc651c18c2c94b09b7db8b1220bf20e9c14d"},
        {uint256_t{
             0xb22176ee483d3035UL,
             0xaf94def32b9d0f98UL,
             0x65829e7450e3797cUL,
             0xffeab2a2c43647e8UL},
         "115754451500915698797016776063775039799476313935046177147294877365978"
         "332475445",
         "ffeab2a2c43647e865829e7450e3797caf94def32b9d0f98b22176ee483d3035"},
        {uint256_t{
             0xffffffffffffffffUL,
             0xffffffffffffffffUL,
             0xffffffffffffffffUL,
             0xffffffffffffffffUL,
         },
         "115792089237316195423570985008687907853269984665640564039457584007913"
         "129639935",
         "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"}};

    for (auto const &[x, dec_str, hex_str] : test_cases) {
        ASSERT_EQ(x.to_string(), dec_str);
        ASSERT_EQ(x.to_string(16), hex_str);

        ASSERT_EQ(uint256_t::from_string(dec_str), x);
        ASSERT_EQ(uint256_t::from_string("0x" + hex_str), x);
    }

    auto const *hex_digit_in_dec =
        "ffeab2a2c43647e865829e7450e3797caf94def32b9d0f98b22176ee483d3035";
    ASSERT_THROW(
        uint256_t::from_string(hex_digit_in_dec), std::invalid_argument);

    auto const *too_many_hex_digits =
        "0xffeab2a2c43647e865829e7450e3797caf94def32b9d0f98b22176ee483d30350";
    ASSERT_THROW(
        uint256_t::from_string(too_many_hex_digits), std::out_of_range);

    auto const *too_many_dec_digits =
        "115754451500915698797016776063775039799476313935046177147294877365978"
        "3324754450";
    ASSERT_THROW(
        uint256_t::from_string(too_many_dec_digits), std::out_of_range);

    auto const *out_of_range_78_digits =
        "115792089237316195423570985008687907853269984665640564039457584007913"
        "129639945";
    ASSERT_THROW(
        uint256_t::from_string(out_of_range_78_digits), std::out_of_range);
}
