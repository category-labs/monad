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
#include <category/core/int.hpp>

#include <type_traits>

MONAD_NAMESPACE_BEGIN

// BigEndian is a strongly typed big endian wrapper. This is used primarily for
// writing to state, to allow for simple conversion to and from big endian.
template <typename T>
    requires(std::is_integral_v<T> || std::is_same_v<T, uint256_t>)
struct BigEndian
{
    unsigned char bytes[sizeof(T)];

    BigEndian() = default;

    BigEndian(T const &x) noexcept
    {
        intx::be::store(bytes, x);
    }

    bool operator==(BigEndian<T> const &other) const noexcept
    {
        return 0 == std::memcmp(this, &other, sizeof(BigEndian<T>));
    }

    T native() const noexcept
    {
        return intx::be::load<T>(bytes);
    }

    BigEndian<T> &operator=(T const &x) noexcept
    {
        intx::be::store(bytes, x);
        return *this;
    }
};

using u16_be = BigEndian<uint16_t>;
using u32_be = BigEndian<uint32_t>;
using u64_be = BigEndian<uint64_t>;
using u256_be = BigEndian<uint256_t>;
static_assert(sizeof(u16_be) == sizeof(uint16_t));
static_assert(sizeof(u32_be) == sizeof(uint32_t));
static_assert(sizeof(u64_be) == sizeof(uint64_t));
static_assert(sizeof(u256_be) == sizeof(uint256_t));

template <typename T>
struct is_big_endian_wrapper : std::false_type
{
};

template <>
struct is_big_endian_wrapper<uint8_t> : std::true_type
{
};

template <typename U>
struct is_big_endian_wrapper<BigEndian<U>> : std::true_type
{
};

template <typename T>
concept BigEndianType = is_big_endian_wrapper<T>::value;

MONAD_NAMESPACE_END
