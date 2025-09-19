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

#include "config.hpp"

#include <concepts>
#include <filesystem>
#include <type_traits>

MONAD_ASYNC_NAMESPACE_BEGIN

//! The types suitable for rounding up or down
template <class T, unsigned bits>
concept safely_roundable_type =
    std::unsigned_integral<T> && (__CHAR_BIT__ * sizeof(T)) > bits;

template <unsigned bits, safely_roundable_type<bits> T>
inline constexpr T round_up_align(T const x) noexcept
{
    constexpr T mask = (T(1) << bits) - 1;
    return (x + mask) & ~mask;
}

template <unsigned bits>
inline constexpr chunk_offset_t round_up_align(chunk_offset_t x) noexcept
{
    constexpr file_offset_t mask = (file_offset_t(1) << bits) - 1;
    x.offset = (x.offset + mask) & ~mask;
    return x;
}

template <unsigned bits, safely_roundable_type<bits> T>
inline constexpr T round_down_align(T const x) noexcept
{
    constexpr T mask = ~((T(1) << bits) - 1);
    return x & mask;
}

template <unsigned bits>
inline constexpr chunk_offset_t round_down_align(chunk_offset_t x) noexcept
{
    constexpr file_offset_t mask = ~((file_offset_t(1) << bits) - 1);
    x.offset = x.offset & mask & chunk_offset_t::max_offset;
    return x;
}

//! Returns a temporary directory in which `O_DIRECT` files definitely work
extern std::filesystem::path const &working_temporary_directory();

//! Creates already deleted file so no need to clean it up
//! after
extern int make_temporary_inode() noexcept;

MONAD_ASYNC_NAMESPACE_END
