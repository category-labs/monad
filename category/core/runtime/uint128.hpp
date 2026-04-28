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

MONAD_NAMESPACE_BEGIN

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

    constexpr explicit operator unsigned __int128() const noexcept
    {
        return (static_cast<unsigned __int128>(hi) << 64) | lo;
    }

    [[nodiscard]] static constexpr uint128_t from_string(char const *const s)
    {
        MONAD_ASSERT(s != nullptr);
        uint128_t result{};
        char const *p = s;
        if (p[0] == '0' && (p[1] == 'x' || p[1] == 'X')) {
            p += 2;
            constexpr size_t max_hex_digits = sizeof(uint128_t) * 2;
            size_t num_digits = 0;
            if (*p == '\0') {
                throw std::invalid_argument(s);
            }
            unsigned __int128 r = 0;
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
                    throw std::invalid_argument(s);
                }
                if (++num_digits > max_hex_digits) {
                    throw std::out_of_range(s);
                }
                r = (r << 4) | d;
                ++p;
            }
            result = {static_cast<uint64_t>(r), static_cast<uint64_t>(r >> 64)};
        }
        else {
            // UINT128_MAX / 10; any result larger than this overflows when
            // multiplied by 10
            constexpr unsigned __int128 max_before_mul10 =
                ((static_cast<unsigned __int128>(
                      std::numeric_limits<uint64_t>::max())
                  << 64) |
                 std::numeric_limits<uint64_t>::max()) /
                10;
            constexpr unsigned __int128 uint128_max =
                (static_cast<unsigned __int128>(
                     std::numeric_limits<uint64_t>::max())
                 << 64) |
                std::numeric_limits<uint64_t>::max();
            if (*p == '\0') {
                throw std::invalid_argument(s);
            }
            unsigned __int128 r = 0;
            while (*p != '\0') {
                if (*p < '0' || *p > '9') {
                    throw std::invalid_argument(s);
                }
                auto const digit = static_cast<uint8_t>(*p - '0');
                if (r > max_before_mul10) {
                    throw std::out_of_range(s);
                }
                r *= 10;
                if (r > uint128_max - digit) {
                    throw std::out_of_range(s);
                }
                r += digit;
                ++p;
            }
            result = {static_cast<uint64_t>(r), static_cast<uint64_t>(r >> 64)};
        }
        return result;
    }
};

// The following five asserts together guarantee that std::bit_cast between
// uint128_t and unsigned __int128 is a lossless round-trip in both
// directions, and that lo maps to the low 64 bits and hi to the high 64
// bits of the native type.
static_assert(alignof(uint128_t) == 8);
static_assert(sizeof(uint128_t) == sizeof(unsigned __int128));
static_assert(
    std::has_unique_object_representations_v<uint128_t>,
    "uint128_t must have no padding to round-trip via bit_cast");
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
operator*(uint128_t const a, uint128_t const b) noexcept
{
    auto const r =
        static_cast<unsigned __int128>(a) * static_cast<unsigned __int128>(b);
    return {static_cast<uint64_t>(r), static_cast<uint64_t>(r >> 64)};
}

[[nodiscard]] constexpr uint128_t
operator/(uint128_t const a, uint64_t const b) noexcept
{
    // Only used in the cold to_string path; unsigned __int128 division is
    // sufficient here (a perf-oriented asm using hardware div was removed as
    // unnecessary for a cold path).
    MONAD_ASSERT(b != 0);
    auto const r = static_cast<unsigned __int128>(a) / b;
    return {static_cast<uint64_t>(r), static_cast<uint64_t>(r >> 64)};
}

[[nodiscard]] constexpr uint128_t
operator>>(uint128_t const x, uint64_t const shift) noexcept
{
    MONAD_ASSERT(shift < 128);
    auto const r = static_cast<unsigned __int128>(x) >> shift;
    return {static_cast<uint64_t>(r), static_cast<uint64_t>(r >> 64)};
}

[[nodiscard]] constexpr uint128_t byteswap(uint128_t const x) noexcept
{
    return {std::byteswap(x.hi), std::byteswap(x.lo)};
}

[[nodiscard]] inline std::string
to_string(uint128_t const v, int const base = 10)
{
    MONAD_ASSERT(base >= 2 && base <= 16);
    static constexpr char digits[] = "0123456789abcdef";
    auto r = static_cast<unsigned __int128>(v);
    if (r == 0) {
        return "0";
    }
    std::string result;
    while (r != 0) {
        result += digits[r % static_cast<unsigned>(base)];
        r /= static_cast<unsigned>(base);
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
