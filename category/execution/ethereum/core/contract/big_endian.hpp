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
#include <category/core/endian.hpp>
#include <category/core/int.hpp>
#include <category/core/unaligned.hpp>

#include <algorithm>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

// BigEndian is a strongly typed big endian wrapper. This is used primarily for
// writing to state, to allow for simple conversion to and from big endian.
template <typename T>
    requires(unsigned_integral<T>)
struct BigEndian
{
    using native_type = T;

    unsigned char bytes[sizeof(T)];

    BigEndian() = default;

    constexpr BigEndian(T const &x) noexcept
    {
        auto const be = intx::bswap(x);
        unaligned_store(bytes, be);
    }

    constexpr bool operator==(BigEndian<T> const &other) const noexcept
    {
        return std::ranges::equal(bytes, other.bytes);
    }

    [[nodiscard]] constexpr native_type native() const noexcept
    {
        return intx::bswap(std::bit_cast<native_type>(bytes));
    }

    constexpr BigEndian<T> &operator=(T const &x) noexcept
    {
        auto const be = intx::bswap(x);
        unaligned_store(bytes, be);
        return *this;
    }
};

using u8_be = BigEndian<uint8_t>;
using u16_be = BigEndian<uint16_t>;
using u32_be = BigEndian<uint32_t>;
using u64_be = BigEndian<uint64_t>;
using u256_be = BigEndian<uint256_t>;
static_assert(sizeof(u8_be) == sizeof(uint8_t));
static_assert(alignof(u8_be) == 1);
static_assert(sizeof(u16_be) == sizeof(uint16_t));
static_assert(alignof(u16_be) == 1);
static_assert(sizeof(u32_be) == sizeof(uint32_t));
static_assert(alignof(u32_be) == 1);
static_assert(sizeof(u64_be) == sizeof(uint64_t));
static_assert(alignof(u64_be) == 1);
static_assert(sizeof(u256_be) == sizeof(uint256_t));
static_assert(alignof(u256_be) == 1);

template <typename T>
struct is_big_endian_wrapper : std::false_type
{
};

template <typename U>
struct is_big_endian_wrapper<BigEndian<U>> : std::true_type
{
};

template <typename T>
concept BigEndianType = is_big_endian_wrapper<T>::value;

MONAD_NAMESPACE_END
