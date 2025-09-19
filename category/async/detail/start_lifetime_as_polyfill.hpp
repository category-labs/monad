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

#include "../config.hpp"

#ifndef MONAD_USE_STD_START_LIFETIME_AS
    #if __cpp_lib_start_lifetime_as >= 202207L
        #define MONAD_USE_STD_START_LIFETIME_AS 1
    #else
        #define MONAD_USE_STD_START_LIFETIME_AS 0
    #endif
#endif

#if MONAD_USE_STD_START_LIFETIME_AS
    #include <memory>
#endif

namespace monad
{
#if MONAD_USE_STD_START_LIFETIME_AS
    using std::start_lifetime_as;
    using std::start_lifetime_as_array;
#else
    template <class T>
    inline T *start_lifetime_as(void *p) noexcept
    {
        return reinterpret_cast<T *>(p);
    }

    template <class T>
    inline T const *start_lifetime_as(void const *p) noexcept
    {
        return reinterpret_cast<T const *>(p);
    }

    template <class T>
    inline T volatile *start_lifetime_as(void volatile *p) noexcept
    {
        return reinterpret_cast<T volatile *>(p);
    }

    template <class T>
    inline T const volatile *start_lifetime_as(void const volatile *p) noexcept
    {
        return reinterpret_cast<T const volatile *>(p);
    }

    template <class T>
    inline T *start_lifetime_as_array(void *p, std::size_t) noexcept
    {
        return reinterpret_cast<T *>(p);
    }

    template <class T>
    inline T const *start_lifetime_as_array(void const *p, std::size_t) noexcept
    {
        return reinterpret_cast<T const *>(p);
    }

    template <class T>
    inline T volatile *
    start_lifetime_as_array(void volatile *p, std::size_t) noexcept
    {
        return reinterpret_cast<T volatile *>(p);
    }

    template <class T>
    inline T const volatile *
    start_lifetime_as_array(void const volatile *p, std::size_t) noexcept
    {
        return reinterpret_cast<T const volatile *>(p);
    }
#endif
}
