#pragma once

#include <monad/config.hpp>

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
