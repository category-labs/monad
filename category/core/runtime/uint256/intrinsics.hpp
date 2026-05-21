// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/core/runtime/uint256/portable.hpp>
#include <category/core/runtime/uint256/types.hpp>

#include <cstdint>
#include <immintrin.h>

#ifndef __AVX2__
    #error "Target architecture must support AVX2"
#endif

#ifndef __BMI2__
    #error "Target architecture must support BMI2 (for MULX)"
#endif

MONAD_NAMESPACE_BEGIN

[[gnu::always_inline]] constexpr inline uint64_t force(uint64_t expr) noexcept
{
    if !consteval {
        asm("" : "+r"(expr));
    }
    return expr;
}

[[gnu::always_inline]]
inline result_with_carry<uint64_t> addc_intrinsic(
    uint64_t const lhs, uint64_t const rhs, bool const carry_in) noexcept
{
    static_assert(sizeof(unsigned long long) == sizeof(uint64_t));
    unsigned long long carry_out = 0;
    uint64_t const sum_carry = __builtin_addcll(lhs, rhs, carry_in, &carry_out);
    return result_with_carry{
        .value = sum_carry, .carry = static_cast<bool>(carry_out)};
}

[[gnu::always_inline]] inline result_with_carry<uint64_t> subb_intrinsic(
    uint64_t const lhs, uint64_t const rhs, bool const borrow_in) noexcept
{
    static_assert(sizeof(unsigned long long) == sizeof(uint64_t));
    unsigned long long borrow_out = 0;
    uint64_t const sub_borrow =
        __builtin_subcll(lhs, rhs, borrow_in, &borrow_out);
    // If we do not force the result here, clang replaces the sub/sbb chain
    // with a long series of comparisons and flag logic which is worse
    return result_with_carry{
        .value = force(sub_borrow), .carry = static_cast<bool>(borrow_out)};
}

[[gnu::always_inline]]
inline uint64_t
shld_intrinsic(uint64_t high, uint64_t const low, uint8_t const shift) noexcept
{
    asm("shldq %[shift], %[low], %[high]"
        : [high] "+r"(high)
        : [low] "r"(low), [shift] "c"(shift)
        : "cc");
    return high;
}

[[gnu::always_inline]]
inline uint64_t
shrd_intrinsic(uint64_t const high, uint64_t low, uint8_t const shift) noexcept
{
    asm("shrdq %[shift], %[high], %[low]"
        : [low] "+r"(low)
        : [high] "r"(high), [shift] "c"(shift)
        : "cc");
    return low;
}

[[gnu::always_inline]]
inline div_result<uint64_t>
div_intrinsic(uint64_t u_hi, uint64_t u_lo, uint64_t const v) noexcept
{
    asm("div %[v]" : "+d"(u_hi), "+a"(u_lo) : [v] "r"(v));
    return {.quot = u_lo, .rem = u_hi};
}

[[gnu::always_inline]]
inline void mulx_intrinsic(
    uint64_t const x, uint64_t const y, uint64_t &r_hi, uint64_t &r_lo) noexcept
{
    /*
    uint64_t hi;
    uint64_t lo;
    */
    asm("mulx %[x], %[lo], %[hi]"
        : [hi] "=r"(r_hi), [lo] "=r"(r_lo)
        : [x] "r"(x), [y] "d"(y));
}

[[gnu::always_inline]]
inline void adc_3(
    uint64_t x_2, uint64_t x_1, uint64_t x_0, uint64_t const y_1,
    uint64_t const y_0, uint64_t &r_2, uint64_t &r_1, uint64_t &r_0) noexcept
{
    asm("addq %[y_0], %[x_0]\n"
        "adcq %[y_1], %[x_1]\n"
        "adcq $0, %[x_2]"
        : [x_0] "+r"(x_0), [x_1] "+r"(x_1), [x_2] "+r"(x_2)
        : [y_0] "r"(y_0), [y_1] "r"(y_1)
        : "cc");
    r_2 = x_2;
    r_1 = x_1;
    r_0 = x_0;
}

[[gnu::always_inline]]
inline void adc_2(
    uint64_t x_1, uint64_t x_0, uint64_t const y_0, uint64_t &r_1,
    uint64_t &r_0) noexcept
{
    asm("addq %[y_0], %[x_0]\n"
        "adcq $0, %[x_1]"
        : [x_0] "+r"(x_0), [x_1] "+r"(x_1)
        : [y_0] "r"(y_0)
        : "cc");
    r_1 = x_1;
    r_0 = x_0;
}

[[gnu::always_inline]]
inline void adc_2(
    uint64_t x_1, uint64_t x_0, uint64_t const y_1, uint64_t const y_0,
    uint64_t &r_1, uint64_t &r_0) noexcept
{
    asm("addq %[y_0], %[x_0]\n"
        "adcq %[y_1], %[x_1]"
        : [x_0] "+r"(x_0), [x_1] "+r"(x_1)
        : [y_0] "r"(y_0), [y_1] "r"(y_1)
        : "cc");
    r_1 = x_1;
    r_0 = x_0;
}

template <size_t I, size_t R, size_t M>
[[gnu::always_inline]]
inline void mul_line_recur(
    words_t<M> const &x, uint64_t const y, words_t<R> &__restrict__ result,
    uint64_t carry) noexcept
{
    if constexpr (I < std::min(R, M)) {
        if constexpr (I + 1 < R) {
            uint64_t hi;
            uint64_t lo;
            mulx(x[I], y, hi, lo);
            adc_2(
                // Input 1
                hi,
                lo,
                // Input 2
                carry,
                // Output
                carry,
                result[I]);
            mul_line_recur<I + 1, R, M>(x, y, result, carry);
        }
        else {
            result[I] = y * x[I] + carry;
        }
    }
    else if constexpr (M < R) {
        result[M] = carry;
    }
}

// result[0 .. min(M + 1, R)) = y * x[0 .. M)
template <size_t R, size_t M>
[[gnu::always_inline]]
inline void mul_line(
    words_t<M> const &x, uint64_t const y,
    words_t<R> &__restrict__ result) noexcept
{
    uint64_t carry;
    mulx(y, x[0], carry, result[0]);

    mul_line_recur<1, R, M>(x, y, result, carry);
}

template <size_t J, size_t I, size_t R, size_t M>
[[gnu::always_inline]]
inline void mul_add_line_recur(
    words_t<M> const &x, uint64_t const y_i, words_t<R> &__restrict__ result,
    uint64_t c_hi, uint64_t c_lo) noexcept
{
    if constexpr (J + 1 < M && I + J < R) {
        if constexpr (I + J + 2 < R) {
            // We need c_lo, c_hi
            uint64_t hi;
            uint64_t lo;
            mulx(x[J + 1], y_i, hi, lo);
            adc_3(
                // Input 1
                hi,
                lo,
                result[I + J],
                // Input 2
                c_hi,
                c_lo,
                // Result
                c_hi,
                c_lo,
                result[I + J]);
        }
        else if constexpr (I + J + 1 < R) {
            // We only need c_lo
            uint64_t const lo = x[J + 1] * y_i;
            adc_2(
                // Input 1
                lo,
                result[I + J],
                // Input 2
                c_hi,
                c_lo,
                // Output
                c_lo,
                result[I + J]);
        }
        else {
            // We're done, we don't need subsequent results
            result[I + J] += c_lo;
        }
        mul_add_line_recur<J + 1, I, R, M>(x, y_i, result, c_hi, c_lo);
    }
    else {
        if constexpr (I + M < R) {

            adc_2(
                // Input 1
                c_hi,
                c_lo,
                // Input 2
                result[I + M - 1],
                // Output
                result[I + M],
                result[I + M - 1]);
        }
        else if constexpr (I + M < R + 1) {
            result[I + M - 1] += c_lo;
        }
    }
}

// result[i .. min(i + M + 1, R)) += y_i * x[0 .. M)
template <size_t I, size_t R, size_t M>
[[gnu::always_inline]]
inline void mul_add_line(
    words_t<M> const &x, uint64_t const y_i,
    words_t<R> &__restrict__ result) noexcept
{
    // A naive implementation would use a single carry variable. However
    // this means on every iteration we compute
    //     result[i+j] = result[i+j] + prod_lo + carry
    // which needs to propagate two carry bits. This causes a slew of
    // setb/xor/movxz instructions to be inserted.
    // Instead, we widen the carry and skew the loop so that every iteration
    // computes
    //     result[i+j] = result[i+j] + c_lo
    //     c_lo = prod_lo + c_hi (+ carry)
    //     c_hi = prod_hi (+ carry)
    uint64_t c_hi;
    uint64_t c_lo;

    if constexpr (I + 1 < R) {
        mulx(x[0], y_i, c_hi, c_lo);
    }
    else {
        c_hi = 0;
        c_lo = x[0] * y_i;
    }
    mul_add_line_recur<0, I, R, M>(x, y_i, result, c_hi, c_lo);
}

template <size_t I, size_t R, size_t M, size_t N>
[[gnu::always_inline]]
inline void truncating_mul_runtime_recur(
    words_t<M> const &x, words_t<N> const &y,
    words_t<R> &__restrict__ result) noexcept
{
    if constexpr (I < N) {
        mul_add_line<I, R, M>(x, y[I], result);
        truncating_mul_runtime_recur<I + 1, R, M>(x, y, result);
    }
}

template <size_t R, size_t M, size_t N>
[[gnu::always_inline]]
inline words_t<R>
truncating_mul_runtime(words_t<M> const &x, words_t<N> const &y) noexcept
    requires(0 < R && 0 < M && 0 < N && R <= M + N)
{
    words_t<R> result;
    mul_line<R>(x, y[0], result);
    truncating_mul_runtime_recur<1, R, M, N>(x, y, result);
    return result;
}

MONAD_NAMESPACE_END
