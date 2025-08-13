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
constexpr inline T *cmemcpy(T *const dst, const T *const src, const size_t num)
{
#if __cpp_lib_is_constant_evaluated >= 201811
    if (std::is_constant_evaluated()) {
#endif
        for (size_t n = 0; n < num; n++) {
            dst[n] = src[n];
        }
#if __cpp_lib_is_constant_evaluated >= 201811
    }
    else {
        std::memcpy(dst, src, num);
    }
#endif
    return dst;
}

//! \brief A constexpr-capable `memcmp`
template <class T>
    requires(sizeof(T) == 1 && std::is_trivially_copyable_v<T>)
constexpr inline int
cmemcmp(const T *const a, const T *const b, const size_t num)
{
#if __cpp_lib_is_constant_evaluated >= 201811
    if (std::is_constant_evaluated()) {
#endif
        for (size_t n = 0; n < num; n++) {
            if (a[n] < b[n]) {
                return -1;
            }
            else if (a[n] > b[n]) {
                return 1;
            }
        }
        return 0;
#if __cpp_lib_is_constant_evaluated >= 201811
    }
    else {
        return std::memcmp(a, b, num);
    }
#endif
}

//! \brief A constexpr-capable `memset`
template <class T>
    requires(sizeof(T) == 1 && std::is_trivially_copyable_v<T>)
constexpr inline T *cmemset(T *const dst, const T value, const size_t num)
{
#if __cpp_lib_is_constant_evaluated >= 201811
    if (std::is_constant_evaluated()) {
#endif
        for (size_t n = 0; n < num; n++) {
            dst[n] = value;
        }
#if __cpp_lib_is_constant_evaluated >= 201811
    }
    else {
        std::memset(dst, (int)value, num);
    }
#endif
    return dst;
}

MONAD_NAMESPACE_END
