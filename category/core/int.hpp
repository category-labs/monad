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

#include <concepts>
#include <limits>

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

using ::intx::to_big_endian;

MONAD_NAMESPACE_END
