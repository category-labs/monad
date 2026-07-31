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

#pragma once

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/throw.hpp>

#include <algorithm>
#include <bit>
#include <climits>
#include <compare>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <string>
#include <type_traits>

// MONAD_HAS_INT128 selects which implementation the two primitives below use.
// Define MONAD_NO_INT128 to take the 32-bit fallback paths on a target that
// does have `unsigned __int128`, so the fallbacks can be tested there; the
// native type itself stays available under __SIZEOF_INT128__ either way.
#if defined(__SIZEOF_INT128__) && !defined(MONAD_NO_INT128)
    #define MONAD_HAS_INT128 1
#endif

MONAD_NAMESPACE_BEGIN

// A 64x64 -> 128 multiply and a 128/64 -> 64 divide are the only two
// operations here that cannot be written in portable C++ without a wider
// integer type. They are isolated as the two primitives below, and use native
// `unsigned __int128` wherever the target has it. Every 64-bit target we build
// for does; 32-bit targets (the rv32im zkVM guest) do not, hence the
// fallbacks. Everything else in this header — and the uint256 arithmetic built
// on it — is written once against these two.

// Full 128-bit product of two 64-bit values, as a (hi, lo) pair.
[[gnu::always_inline]] constexpr inline void mul64x64(
    uint64_t const x, uint64_t const y, uint64_t &r_hi, uint64_t &r_lo) noexcept
{
#if defined(MONAD_HAS_INT128)
    auto const prod =
        static_cast<unsigned __int128>(x) * static_cast<unsigned __int128>(y);
    r_hi = static_cast<uint64_t>(prod >> 64);
    r_lo = static_cast<uint64_t>(prod);
#else
    // Schoolbook multiply over 32-bit halves.
    uint64_t const x_lo = x & 0xffffffff;
    uint64_t const x_hi = x >> 32;
    uint64_t const y_lo = y & 0xffffffff;
    uint64_t const y_hi = y >> 32;

    uint64_t const ll = x_lo * y_lo;
    uint64_t const lh = x_lo * y_hi;
    uint64_t const hl = x_hi * y_lo;
    uint64_t const hh = x_hi * y_hi;

    uint64_t const mid = (ll >> 32) + (lh & 0xffffffff) + (hl & 0xffffffff);
    r_lo = (ll & 0xffffffff) | (mid << 32);
    r_hi = hh + (lh >> 32) + (hl >> 32) + (mid >> 32);
#endif
}

// Quotient and remainder of the 128-bit value (u_hi, u_lo) divided by v.
//
// The quotient is truncated to 64 bits, so callers must ensure u_hi < v for it
// to be exact. Every caller does: Knuth's normalization establishes it in
// long_div/knuth_div, and divmod below reduces the high word first.
[[gnu::always_inline]] constexpr inline void div128by64(
    uint64_t const u_hi, uint64_t const u_lo, uint64_t const v, uint64_t &quot,
    uint64_t &rem) noexcept
{
    MONAD_DEBUG_ASSERT(v != 0);
    MONAD_DEBUG_ASSERT(u_hi < v);
#if defined(MONAD_HAS_INT128)
    auto const u = (static_cast<unsigned __int128>(u_hi) << 64) | u_lo;
    quot = static_cast<uint64_t>(u / v);
    rem = static_cast<uint64_t>(u % v);
#else
    // Restoring binary long division, one quotient bit per iteration: slow,
    // but small and easy to check. Targets without `unsigned __int128` have no
    // hardware 64-bit divide either, so the native path is a libgcc loop for
    // them regardless.
    uint64_t q = 0;
    uint64_t r = u_hi;
    for (int i = 63; i >= 0; --i) {
        // Shifting a 1 out of the top of r means the true partial remainder is
        // 2^64 + r, which always exceeds v.
        bool const overflow = (r >> 63) != 0;
        r = (r << 1) | ((u_lo >> i) & 1);
        if (overflow || r >= v) {
            r -= v;
            q |= uint64_t{1} << i;
        }
    }
    quot = q;
    rem = r;
#endif
}

struct uint128_t
{
    uint64_t lo{};
    uint64_t hi{};

    constexpr uint128_t() noexcept = default;

    template <typename T>
    constexpr explicit(false) uint128_t(T const v) noexcept
        requires std::is_convertible_v<T, uint64_t>
        : lo(static_cast<uint64_t>(v))
        , hi(0)
    {
    }

    constexpr uint128_t(uint64_t const lo, uint64_t const hi) noexcept
        : lo(lo)
        , hi(hi)
    {
    }

    constexpr explicit operator uint64_t() const noexcept
    {
        return lo;
    }

#if defined(__SIZEOF_INT128__)
    constexpr explicit operator unsigned __int128() const noexcept
    {
        return (static_cast<unsigned __int128>(hi) << 64) | lo;
    }
#endif

    // Defined out of line below, because it is written in terms of the
    // operators that follow this class.
    [[nodiscard]] static constexpr uint128_t from_string(char const *s);
};

static_assert(alignof(uint128_t) == 8);
static_assert(sizeof(uint128_t) == 16);
static_assert(
    std::has_unique_object_representations_v<uint128_t>,
    "uint128_t must have no padding to round-trip via bit_cast");

#if defined(__SIZEOF_INT128__)
// Together with the two asserts above, these guarantee that std::bit_cast
// between uint128_t and unsigned __int128 is a lossless round-trip in both
// directions, and that lo maps to the low 64 bits and hi to the high 64 bits
// of the native type.
static_assert(sizeof(uint128_t) == sizeof(unsigned __int128));
static_assert(
    std::has_unique_object_representations_v<unsigned __int128>,
    "unsigned __int128 must have no padding to round-trip via bit_cast");
static_assert(
    [] {
        unsigned __int128 const native =
            (static_cast<unsigned __int128>(2) << 64) | 1;
        auto const s = std::bit_cast<uint128_t>(native);
        return s.lo == 1 && s.hi == 2;
    }(),
    "uint128_t lo/hi fields must match the layout of unsigned __int128");
#endif

// Only the operations required by current callers are provided.

[[nodiscard]] constexpr bool
operator==(uint128_t const a, uint128_t const b) noexcept
{
    return a.lo == b.lo && a.hi == b.hi;
}

[[nodiscard]] constexpr uint128_t operator~(uint128_t const x) noexcept
{
    return {~x.lo, ~x.hi};
}

[[nodiscard]] constexpr std::strong_ordering
operator<=>(uint128_t const a, uint128_t const b) noexcept
{
    if (auto c = a.hi <=> b.hi; c != 0) {
        return c;
    }
    return a.lo <=> b.lo;
}

[[nodiscard]] constexpr uint128_t
operator+(uint128_t const a, uint128_t const b) noexcept
{
    uint64_t const lo = a.lo + b.lo;
    return {lo, a.hi + b.hi + (lo < a.lo)};
}

[[nodiscard]] constexpr uint128_t
operator-(uint128_t const a, uint128_t const b) noexcept
{
    uint64_t const lo = a.lo - b.lo;
    return {lo, a.hi - b.hi - (lo > a.lo)};
}

[[nodiscard]] constexpr uint128_t
operator&(uint128_t const a, uint128_t const b) noexcept
{
    return {a.lo & b.lo, a.hi & b.hi};
}

[[nodiscard]] constexpr uint128_t
operator|(uint128_t const a, uint128_t const b) noexcept
{
    return {a.lo | b.lo, a.hi | b.hi};
}

[[nodiscard]] constexpr uint128_t
operator*(uint128_t const a, uint128_t const b) noexcept
{
    uint64_t hi = 0;
    uint64_t lo = 0;
    mul64x64(a.lo, b.lo, hi, lo);
    // The a.hi * b.hi term contributes only above bit 127, so it is dropped.
    return {lo, hi + a.lo * b.hi + a.hi * b.lo};
}

[[nodiscard]] constexpr uint128_t
operator<<(uint128_t const x, uint64_t const shift) noexcept
{
    MONAD_ASSERT(shift < 128);
    if (shift == 0) {
        return x;
    }
    if (shift >= 64) {
        return {0, x.lo << (shift - 64)};
    }
    return {x.lo << shift, (x.hi << shift) | (x.lo >> (64 - shift))};
}

[[nodiscard]] constexpr uint128_t
operator>>(uint128_t const x, uint64_t const shift) noexcept
{
    MONAD_ASSERT(shift < 128);
    if (shift == 0) {
        return x;
    }
    if (shift >= 64) {
        return {x.hi >> (shift - 64), 0};
    }
    return {(x.lo >> shift) | (x.hi << (64 - shift)), x.hi >> shift};
}

constexpr uint128_t &operator&=(uint128_t &a, uint128_t const b) noexcept
{
    a = a & b;
    return a;
}

constexpr uint128_t &operator|=(uint128_t &a, uint128_t const b) noexcept
{
    a = a | b;
    return a;
}

constexpr uint128_t &operator-=(uint128_t &a, uint128_t const b) noexcept
{
    a = a - b;
    return a;
}

constexpr uint128_t operator--(uint128_t &x, int) noexcept
{
    auto const old = x;
    x -= 1;
    return old;
}

// Quotient of a / b, with the remainder written to `rem`.
[[nodiscard]] constexpr uint128_t
divmod(uint128_t const a, uint64_t const b, uint64_t &rem) noexcept
{
    MONAD_ASSERT(b != 0);
    // div128by64 needs a high word below the divisor, so reduce it first when
    // the quotient does not fit in a single word.
    uint64_t quot_lo = 0;
    if (a.hi < b) {
        div128by64(a.hi, a.lo, b, quot_lo, rem);
        return {quot_lo, 0};
    }
    div128by64(a.hi % b, a.lo, b, quot_lo, rem);
    return {quot_lo, a.hi / b};
}

[[nodiscard]] constexpr uint128_t
operator/(uint128_t const a, uint64_t const b) noexcept
{
    uint64_t rem = 0;
    return divmod(a, b, rem);
}

// `static_cast<__int128>(x) >> 64` reinterpreted as unsigned: the high word
// sign-extended across all 128 bits. Used for borrow propagation in knuth_div.
[[nodiscard]] constexpr uint128_t
arithmetic_shift_right_64(uint128_t const x) noexcept
{
    return {x.hi, (x.hi >> 63) != 0 ? ~uint64_t{0} : uint64_t{0}};
}

[[nodiscard]] constexpr uint128_t byteswap(uint128_t const x) noexcept
{
    return {std::byteswap(x.hi), std::byteswap(x.lo)};
}

constexpr uint128_t uint128_t::from_string(char const *const s)
{
    MONAD_ASSERT(s != nullptr);
    uint128_t r{};
    char const *p = s;
    if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X')) {
        p += 2;
        constexpr size_t max_hex_digits = sizeof(uint128_t) * 2;
        size_t num_digits = 0;
        if (*p == '\0') {
            MONAD_THROW(std::invalid_argument, s);
        }
        while (*p != '\0') {
            uint8_t d;
            if (*p >= '0' && *p <= '9') {
                d = static_cast<uint8_t>(*p - '0');
            }
            else if (*p >= 'a' && *p <= 'f') {
                d = static_cast<uint8_t>(*p - 'a' + 10);
            }
            else if (*p >= 'A' && *p <= 'F') {
                d = static_cast<uint8_t>(*p - 'A' + 10);
            }
            else {
                MONAD_THROW(std::invalid_argument, s);
            }
            if (++num_digits > max_hex_digits) {
                MONAD_THROW(std::out_of_range, s);
            }
            r = (r << 4) | d;
            ++p;
        }
    }
    else {
        constexpr uint128_t uint128_max = ~uint128_t{};
        // Any value above this overflows when multiplied by 10.
        constexpr uint128_t max_before_mul10 = uint128_max / 10;
        if (*p == '\0') {
            MONAD_THROW(std::invalid_argument, s);
        }
        while (*p != '\0') {
            if (*p < '0' || *p > '9') {
                MONAD_THROW(std::invalid_argument, s);
            }
            auto const digit = static_cast<uint8_t>(*p - '0');
            if (r > max_before_mul10) {
                MONAD_THROW(std::out_of_range, s);
            }
            r = r * 10;
            if (r > uint128_max - digit) {
                MONAD_THROW(std::out_of_range, s);
            }
            r = r + digit;
            ++p;
        }
    }
    return r;
}

[[nodiscard]] inline std::string
to_string(uint128_t const v, int const base = 10)
{
    MONAD_ASSERT(base >= 2 && base <= 16);
    static constexpr char digits[] = "0123456789abcdef";
    if (v == 0) {
        return "0";
    }
    std::string result;
    uint128_t r = v;
    while (r != 0) {
        uint64_t rem = 0;
        r = divmod(r, static_cast<uint64_t>(base), rem);
        result += digits[rem];
    }
    std::reverse(result.begin(), result.end());
    return result;
}

[[nodiscard]] consteval uint128_t operator""_u128(char const *const s)
{
    return uint128_t::from_string(s);
}

MONAD_NAMESPACE_END

template <>
struct std::numeric_limits<monad::uint128_t>
{
    using type = monad::uint128_t;

    static constexpr bool is_specialized = true;
    static constexpr bool is_integer = true;
    static constexpr bool is_signed = false;
    static constexpr bool is_exact = true;
    static constexpr bool has_infinity = false;
    static constexpr bool has_quiet_NaN = false;
    static constexpr bool has_signaling_NaN = false;
    static constexpr float_denorm_style has_denorm = std::denorm_absent;
    static constexpr bool has_denorm_loss = false;
    static constexpr float_round_style round_style = std::round_toward_zero;
    static constexpr bool is_iec559 = false;
    static constexpr bool is_bounded = true;
    static constexpr bool is_modulo = true;
    static constexpr int digits = CHAR_BIT * sizeof(type);
    static constexpr int digits10 = int(0.3010299956639812 * digits);
    static constexpr int max_digits10 = 0;
    static constexpr int radix = 2;
    static constexpr int min_exponent = 0;
    static constexpr int min_exponent10 = 0;
    static constexpr int max_exponent = 0;
    static constexpr int max_exponent10 = 0;
    static constexpr bool traps = std::numeric_limits<unsigned>::traps;
    static constexpr bool tinyness_before = false;

    static constexpr type max() noexcept
    {
        return ~type{};
    }

    static constexpr type min() noexcept
    {
        return {};
    }

    static constexpr type lowest() noexcept
    {
        return min();
    }

    static constexpr type epsilon() noexcept
    {
        return {};
    }

    static constexpr type round_error() noexcept
    {
        return {};
    }

    static constexpr type infinity() noexcept
    {
        return {};
    }

    static constexpr type quiet_NaN() noexcept
    {
        return {};
    }

    static constexpr type signaling_NaN() noexcept
    {
        return {};
    }

    static constexpr type denorm_min() noexcept
    {
        return {};
    }
};
