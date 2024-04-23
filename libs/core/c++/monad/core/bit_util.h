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
