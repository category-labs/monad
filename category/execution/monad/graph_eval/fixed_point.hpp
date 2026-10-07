// Copyright (C) 2026 Category Labs, Inc.
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

#pragma once

#include <category/execution/monad/graph_eval/config.hpp>

#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <type_traits>

// Arithmetic on fixed-point numbers: integers of any dtype read as multiples of
// 2^-bits, where `bits`, the number of fractional bits, is an op parameter of
// at most MAX_FRACTIONAL_BITS. Everything is integer arithmetic, so results are
// the same on every machine; each function says how it rounds.

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// A two's complement type in which the product of two T's, or a T shifted left
// by up to 63 bits, is exact
template <typename T>
using fixed_point_wide_t =
    std::conditional_t<std::is_signed_v<T>, __int128, unsigned __int128>;

// floor(a * b / 2^bits), wrapping to T. The product is exact, in 64 bits for
// types up to 32 bits wide and in 128 bits otherwise
template <typename T>
[[gnu::always_inline]]
inline T q_mul(T const a, T const b, unsigned const bits)
{
    using Wide = std::conditional_t<
        sizeof(T) <= 4,
        std::conditional_t<std::is_signed_v<T>, int64_t, uint64_t>,
        fixed_point_wide_t<T>>;
    return static_cast<T>(static_cast<Wide>(a) * static_cast<Wide>(b) >> bits);
}

// a * 2^bits / b, truncated toward zero and wrapping to T, for a nonzero b. The
// shifted dividend is exact, and so is the quotient, which is no larger
template <typename T>
[[gnu::always_inline]]
inline T q_div(T const a, T const b, unsigned const bits)
{
    using Wide = fixed_point_wide_t<T>;
    return static_cast<T>(
        (static_cast<Wide>(a) << bits) / static_cast<Wide>(b));
}

// ln 2 with 64 fractional bits, rounded to nearest
inline constexpr uint64_t LN2_Q64 = 0xb17217f7d1cf79ac;

// The terms of Taylor's series q_exp sums
inline constexpr size_t EXP_TERMS = 21;

// 2^63 / n!, rounded down, for n < EXP_TERMS: the series' coefficients, with 63
// fractional bits. 20! is less than 2^63
inline constexpr std::array<uint64_t, EXP_TERMS> EXP_COEFFICIENTS = [] {
    std::array<uint64_t, EXP_TERMS> coefficients{};
    uint64_t factorial = 1;
    for (uint64_t n = 0; n < EXP_TERMS; n++) {
        factorial *= n == 0 ? 1 : n;
        coefficients[n] = (uint64_t{1} << 63) / factorial;
    }
    return coefficients;
}();

// e^EXP_LIMIT is more than 2^64, and e^-EXP_LIMIT * 2^63 less than 1, so
// q_exp's result for any input at least this far from 0 is past every dtype's
// range, or rounds down to 0, whatever the number of fractional bits
inline constexpr int EXP_LIMIT = 45;

// e^(x / 2^bits) * 2^bits, rounded down, saturating at T's largest value.
//
// x / 2^bits, with 64 fractional bits, is split into k ln 2 + r, with r in
// [0, ln 2), so that the result is e^r * 2^(k + bits). e^r, which is in [1, 2),
// is the sum of the series' first EXP_TERMS terms by Horner's rule, with 63
// fractional bits, each step rounding down. The terms left out are less than
// one unit in the last place
template <typename T>
inline T q_exp(T const x, unsigned const bits)
{
    using i128 = __int128;
    using u128 = unsigned __int128;
    constexpr T max = std::numeric_limits<T>::max();
    i128 const value = x;
    i128 const limit = i128{EXP_LIMIT} << bits;
    if (value >= limit) {
        return max;
    }
    if (value <= -limit) {
        return 0;
    }

    // Less than EXP_LIMIT * 2^64 in magnitude, so k is in [-65, 64]
    i128 const v = value << (64 - bits);
    i128 const ln2 = LN2_Q64;
    i128 k = v / ln2;
    i128 r = v - k * ln2;
    if (r < 0) {
        k -= 1;
        r += ln2;
    }

    // Below 2^64, since every step rounds down and e^r is below 2
    uint64_t const r63 = static_cast<uint64_t>(r >> 1);
    uint64_t p = EXP_COEFFICIENTS[EXP_TERMS - 1];
    for (size_t n = EXP_TERMS - 1; n-- > 0;) {
        p = EXP_COEFFICIENTS[n] + static_cast<uint64_t>(u128{p} * r63 >> 63);
    }

    // The result is p * 2^shift, and p is at least 2^63, so a positive shift
    // makes it at least 2^64
    int64_t const shift = static_cast<int64_t>(k) + bits - 63;
    if (shift > 0) {
        return max;
    }
    uint64_t const result = shift <= -64 ? 0 : p >> -shift;
    return result > static_cast<uint64_t>(max) ? max : static_cast<T>(result);
}

// floor(sqrt(n)), by Newton's method from above
inline uint64_t isqrt(unsigned __int128 const n)
{
    using u128 = unsigned __int128;
    if (n == 0) {
        return 0;
    }
    auto const high = static_cast<uint64_t>(n >> 64);
    int const width = high != 0
                          ? 128 - std::countl_zero(high)
                          : 64 - std::countl_zero(static_cast<uint64_t>(n));
    // At least sqrt(n), and at most 2^64, so x + n / x can't overflow
    u128 x = u128{1} << ((width + 1) / 2);
    for (;;) {
        u128 const y = (x + n / x) >> 1;
        if (y >= x) {
            return static_cast<uint64_t>(x);
        }
        x = y;
    }
}

// 2^bits / sqrt(x / 2^bits), rounded down, saturating at T's largest value, for
// a positive x. That's floor(sqrt(2^(3 bits) / x)), which is also
// floor(sqrt(floor(2^(3 bits) / x))), as computed here, exactly
template <typename T>
inline T q_inv_sqrt(T const x, unsigned const bits)
{
    using u128 = unsigned __int128;
    constexpr T max = std::numeric_limits<T>::max();
    auto const divisor = static_cast<uint64_t>(x);
    unsigned const exponent = 3 * bits;
    u128 quotient;
    if (exponent < 128) {
        quotient = (u128{1} << exponent) / divisor;
    }
    else {
        // The quotient is at least 2^128, and its root at least 2^64, past
        // every dtype's range, when the divisor is at most 2^(exponent - 128)
        if (divisor <= uint64_t{1} << (exponent - 128)) {
            return max;
        }
        // Otherwise it's below 2^128: divide 2^(exponent - 64) by the
        // divisor, then 2^64 times the remainder, which is below 2^128
        u128 const dividend = u128{1} << (exponent - 64);
        u128 const high = dividend / divisor;
        u128 const remainder = dividend % divisor;
        quotient = (high << 64) | ((remainder << 64) / divisor);
    }
    uint64_t const root = isqrt(quotient);
    return root > static_cast<uint64_t>(max) ? max : static_cast<T>(root);
}

MONAD_GRAPH_EVAL_NAMESPACE_END
