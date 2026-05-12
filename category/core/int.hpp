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
#include <category/core/hex.hpp>
#include <category/core/runtime/uint128.hpp>
#include <category/core/runtime/uint256.hpp>

#include <bit>
#include <concepts>
#include <cstdint>
#include <cstring>
#include <limits>
#include <string>
#include <type_traits>

static_assert(
    std::endian::native == std::endian::little,
    "monad integer utilities require a little-endian platform");

MONAD_NAMESPACE_BEGIN

static_assert(sizeof(uint128_t) == 16);
static_assert(alignof(uint128_t) == 8);

static_assert(sizeof(uint256_t) == 32);
static_assert(alignof(uint256_t) == 8);

template <class T>
concept unsigned_integral =
    std::unsigned_integral<T> || std::same_as<uint128_t, T> ||
    std::same_as<uint256_t, T>;

[[nodiscard]] inline std::string to_string(uint256_t const &v, int base = 10)
{
    return v.to_string(base);
}

template <typename T>
[[nodiscard]] inline T from_string(std::string const &s)
{
    if constexpr (std::same_as<T, uint256_t>) {
        return uint256_t::from_string(s.c_str());
    }
    else if constexpr (std::same_as<T, uint128_t>) {
        return uint128_t::from_string(s.c_str());
    }
    else {
        static_assert(
            sizeof(T) == 0, "from_string not supported for this type");
    }
}

template <typename T>
[[nodiscard]] inline uint8_t *as_bytes(T &x) noexcept
{
    static_assert(std::is_trivially_copyable_v<T>);
    return reinterpret_cast<uint8_t *>(&x);
}

template <typename T>
[[nodiscard]] inline uint8_t const *as_bytes(T const &x) noexcept
{
    static_assert(std::is_trivially_copyable_v<T>);
    return reinterpret_cast<uint8_t const *>(&x);
}

template <typename T>
[[nodiscard]] inline constexpr T bswap(T const x) noexcept
{
    if constexpr (std::same_as<T, uint256_t>) {
        return byteswap(x);
    }
    else if constexpr (std::same_as<T, uint128_t>) {
        return byteswap(x);
    }
    else if constexpr (std::unsigned_integral<T>) {
        return std::byteswap(x);
    }
    else {
        static_assert(sizeof(T) == 0, "bswap not supported for this type");
    }
}

template <typename T>
[[nodiscard]] inline constexpr T to_big_endian(T const x) noexcept
{
    return bswap(x);
}

// Load a big-endian encoded integer from an unaligned byte buffer.
template <typename T>
[[nodiscard]] inline T load_be_unsafe(uint8_t const *src) noexcept
{
    static_assert(std::is_trivially_copyable_v<T>);
    T x;
    std::memcpy(&x, src, sizeof(x));
    return bswap(x);
}

// Load a big-endian encoded integer from a struct with a .bytes member.
template <typename T, FixedBytes Src>
[[nodiscard]] inline T load_be(Src const &src) noexcept
{
    static_assert(sizeof(Src::bytes) == sizeof(T));
    return load_be_unsafe<T>(src.bytes);
}

// Store an integer as big-endian bytes into an unaligned byte buffer.
template <typename T>
inline void store_be(uint8_t *dst, T const x) noexcept
{
    T const be = bswap(x);
    std::memcpy(dst, &be, sizeof(be));
}

// Store an integer as big-endian bytes into a new value of type DstT
// (which must have a .bytes member of matching size).
template <FixedBytes DstT, typename SrcT>
[[nodiscard]] inline DstT store_be_as(SrcT const x) noexcept
{
    static_assert(sizeof(DstT::bytes) == sizeof(SrcT));
    DstT dst{};
    store_be(dst.bytes, x);
    return dst;
}

MONAD_NAMESPACE_END

namespace monad::literals
{
    using monad::operator""_u256;
    using monad::operator""_u128;
}
