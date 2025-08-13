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

/**
 * finds the largest integer n such that n * 2^b <= x
 */
[[gnu::always_inline]] static inline unsigned long
bit_div_floor(unsigned long const x, unsigned long const b)
{
    return x >> b;
}

/**
 * finds the smallest integer n such that n * 2^b >= x
 *
 * @warning overflow possible
 */
[[gnu::always_inline]] static inline unsigned long
bit_div_ceil(unsigned long const x, unsigned long const b)
{
    unsigned long const m = (1UL << b) - 1;
    return bit_div_floor(x + m, b);
}

/**
 * finds the largest integer n such that n <= x and n is a multiple of 2^b
 */
[[gnu::always_inline]] static inline unsigned long
bit_round_down(unsigned long const x, unsigned long const b)
{
    return bit_div_floor(x, b) << b;
}

/**
 * finds the smallest integer n such that n >= x and n is a multiple of 2^b
 *
 * @warning overflow possible
 */
[[gnu::always_inline]] static inline unsigned long
bit_round_up(unsigned long const x, unsigned long const b)
{
    return bit_div_ceil(x, b) << b;
}
