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

#pragma once

#include <category/core/config.hpp>

#include <intx/intx.hpp>

#include <bit>
#include <concepts>
#include <cstddef>
#include <cstring>
#include <limits>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

using uint128_t = ::intx::uint128;

static_assert(sizeof(uint128_t) == 16);
static_assert(alignof(uint128_t) == 8);

using uint256_t = ::intx::uint256;

static_assert(sizeof(uint256_t) == 32);
static_assert(alignof(uint256_t) == 8);

using uint512_t = ::intx::uint512;

static_assert(sizeof(uint512_t) == 64);
static_assert(alignof(uint512_t) == 8);

template <class T>
concept unsigned_integral =
    std::unsigned_integral<T> || std::same_as<uint128_t, T> ||
    std::same_as<uint256_t, T> || std::same_as<uint512_t, T>;

inline constexpr uint128_t UINT128_MAX = std::numeric_limits<uint128_t>::max();

inline constexpr uint256_t UINT256_MAX = std::numeric_limits<uint256_t>::max();

inline constexpr uint512_t UINT512_MAX = std::numeric_limits<uint512_t>::max();

// Two overloads: one for stdlib unsigned types (uint8_t-uint64_t) using
// std::byteswap, and one for intx multi-word types (uint128_t-uint512_t) which
// must reverse words and byteswap each word. The requires clause on the second
// overload excludes stdlib types to avoid ambiguity.
template <std::unsigned_integral T>
[[nodiscard]] constexpr T to_big_endian(T const x) noexcept
{
    static_assert(
        std::endian::native == std::endian::little,
        "to_big_endian assumes little-endian platform");
    return std::byteswap(x);
}

template <unsigned_integral T>
    requires(!std::unsigned_integral<T>)
[[nodiscard]] constexpr T to_big_endian(T const x) noexcept
{
    static_assert(
        std::endian::native == std::endian::little,
        "to_big_endian assumes little-endian platform");
    T result{};
    for (size_t i = 0; i < T::num_words; ++i) {
        result[i] = std::byteswap(x[T::num_words - 1 - i]);
    }
    return result;
}

// Load a native integer from sizeof(T) big-endian bytes stored in src.
template <unsigned_integral T, typename Src>
    requires(sizeof(Src) == sizeof(T))
[[nodiscard]] T be_load(Src const &src) noexcept
{
    static_assert(std::has_unique_object_representations_v<T>);
    static_assert(std::has_unique_object_representations_v<Src>);
    T result{};
    std::memcpy(
        static_cast<void *>(&result),
        static_cast<void const *>(&src),
        sizeof(T));
    return monad::to_big_endian(result);
}

// Load a native integer from sizeof(T) big-endian bytes at src (no size check).
template <unsigned_integral T>
[[nodiscard]] T be_load(void const *const src) noexcept
{
    static_assert(std::has_unique_object_representations_v<T>);
    T result{};
    std::memcpy(&result, src, sizeof(T));
    return monad::to_big_endian(result);
}

// Store a native integer as big-endian bytes, returning a new Dst.
template <typename Dst, unsigned_integral Src>
    requires(sizeof(Dst) == sizeof(Src))
[[nodiscard]] Dst be_store(Src const value) noexcept
{
    static_assert(std::has_unique_object_representations_v<Dst>);
    auto const be = monad::to_big_endian(value);
    Dst dst{};
    std::memcpy(
        static_cast<void *>(&dst), static_cast<void const *>(&be), sizeof(be));
    return dst;
}

// Store a native integer as big-endian bytes in-place at dst.
template <unsigned_integral Src>
void be_store(void *const dst, Src const value) noexcept
{
    auto const be = monad::to_big_endian(value);
    std::memcpy(dst, &be, sizeof(be));
}

MONAD_NAMESPACE_END
