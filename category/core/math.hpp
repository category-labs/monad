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

#include <concepts>

MONAD_NAMESPACE_BEGIN

/**
 * returns smallest z such that z % y == 0 and z >= x
 */
template <std::unsigned_integral T>
constexpr T round_up(T const x, T const y)
{
    T z = x + (y - 1);
    z /= y;
    z *= y;
    return z;
    /*
        TODO alt impl
        T z = x;
        T const r = x % y;
        if (r) {
            z += y - r;
        }
    */
    return z;
}

MONAD_NAMESPACE_END
