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

#include <cstring> // for memcpy
#include <type_traits>

MONAD_NAMESPACE_BEGIN

//! \brief A constexpr-capable `memcpy`
template <class T>
    requires(sizeof(T) == 1 && std::is_trivially_copyable_v<T>)
inline constexpr T *cmemcpy(T *const dst, T const *const src, size_t const num)
{
    if constexpr (std::is_constant_evaluated()) {
        for (size_t n = 0; n < num; n++) {
            dst[n] = src[n];
        }
    }
    else {
        std::memcpy(dst, src, num);
    }
    return dst;
}

//! \brief A constexpr-capable `memset`
template <class T>
    requires(sizeof(T) == 1 && std::is_trivially_copyable_v<T>)
inline constexpr T *cmemset(T *const dst, T const value, size_t const num)
{
    if constexpr (std::is_constant_evaluated()) {
        for (size_t n = 0; n < num; n++) {
            dst[n] = value;
        }
    }
    else {
        std::memset(dst, (int)value, num);
    }
    return dst;
}

MONAD_NAMESPACE_END
