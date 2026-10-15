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
#include <category/core/runtime/uint128.hpp>
#include <category/core/runtime/uint256/types.hpp>

#include <bit>
#include <cstddef>
#include <cstdint>

// This header file provides constexpr-compatible C++ implementations of the
// binary operations (add, minus, times, division, left shift, and right shift)
// used by the uint256 implementation,

namespace monad::uint256::portable
{

    [[gnu::always_inline]]
    constexpr result_with_carry<uint64_t>
    addc(uint64_t const lhs, uint64_t const rhs, bool const carry_in) noexcept
    {
        uint64_t const sum = lhs + rhs;
        bool carry_out = sum < lhs;
        uint64_t const sum_carry = sum + carry_in;
        carry_out |= sum_carry < sum;
        return result_with_carry{.value = sum_carry, .carry = carry_out};
    }

    [[gnu::always_inline]] constexpr result_with_carry<uint64_t>
    subb(uint64_t const lhs, uint64_t const rhs, bool const borrow_in) noexcept
    {
        uint64_t const sub = lhs - rhs;
        bool borrow_out = rhs > lhs;
        uint64_t const sub_borrow = sub - borrow_in;
        borrow_out |= borrow_in > sub;
        return result_with_carry{.value = sub_borrow, .carry = borrow_out};
    }

    [[gnu::always_inline]]
    constexpr uint64_t
    shld(uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        return (high << shift) | ((low >> 1) >> (63 - shift));
    }

    [[gnu::always_inline]]
    constexpr uint64_t
    shrd(uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        return (low >> shift) | ((high << 1) << (63 - shift));
    }

#ifndef __SIZEOF_INT128__
    // 64-by-32-bit division with a 32-bit quotient, u1 < v: Hacker's Delight's
    // divlu on 16-bit half digits, all in 32-bit arithmetic (two divu).
    [[gnu::always_inline]] constexpr uint32_t divlu32(
        uint32_t const u1, uint32_t const u0, uint32_t v, uint32_t &rem) noexcept
    {
        constexpr uint32_t b = uint32_t{1} << 16;
        auto const s = static_cast<unsigned>(std::countl_zero(v));
        v <<= s;
        uint32_t const vn1 = v >> 16;
        uint32_t const vn0 = v & 0xffff;
        uint32_t const un32 = s == 0 ? u1 : (u1 << s) | (u0 >> (32 - s));
        uint32_t const un10 = u0 << s;
        uint32_t const un1 = un10 >> 16;
        uint32_t const un0 = un10 & 0xffff;
        uint32_t q1 = un32 / vn1;
        uint32_t rhat = un32 - q1 * vn1;
        while (q1 >= b || q1 * vn0 > b * rhat + un1) {
            --q1;
            rhat += vn1;
            if (rhat >= b) {
                break;
            }
        }
        uint32_t const un21 = un32 * b + un1 - q1 * v;
        uint32_t q0 = un21 / vn1;
        rhat = un21 - q0 * vn1;
        while (q0 >= b || q0 * vn0 > b * rhat + un0) {
            --q0;
            rhat += vn1;
            if (rhat >= b) {
                break;
            }
        }
        rem = (un21 * b + un0 - q0 * v) >> s;
        return q1 * b + q0;
    }
#endif

    [[gnu::always_inline]]
    constexpr div_result<uint64_t>
    div(uint64_t u_hi, uint64_t u_lo, uint64_t const v) noexcept
    {
#ifdef __SIZEOF_INT128__
        using u128 = unsigned __int128;
        auto const u = static_cast<u128>(uint128_t{u_lo, u_hi});
        auto const quot = static_cast<uint64_t>(u / v);
        auto const rem = static_cast<uint64_t>(u % v);
        return {.quot = quot, .rem = rem};
#else
        // No 128-bit integer type (rv32): Knuth's algorithm D on 32-bit
        // digits, two quotient digits of a normalized two-digit divisor. Each
        // digit's estimate is one 64-by-32-bit division done with two 32-bit
        // divu (divlu32), so nothing calls the runtime's 64-bit division.
        // Requires u_hi < v, which every caller guarantees.
        auto const s = static_cast<unsigned>(std::countl_zero(v));
        uint64_t const vn = v << s;
        uint64_t const un_hi = s == 0 ? u_hi : (u_hi << s) | (u_lo >> (64 - s));
        uint64_t const un_lo = u_lo << s;
        uint32_t const v1 = static_cast<uint32_t>(vn >> 32);
        uint32_t const v0 = static_cast<uint32_t>(vn);
        uint32_t u[4] = {
            static_cast<uint32_t>(un_lo),
            static_cast<uint32_t>(un_lo >> 32),
            static_cast<uint32_t>(un_hi),
            static_cast<uint32_t>(un_hi >> 32)};
        uint32_t q[2] = {0, 0};
        for (int j = 1; j >= 0; --j) {
            auto const jx = static_cast<size_t>(j);
            uint32_t qhat;
            uint32_t rhat;
            bool rhat_overflow = false; // rhat >= 2^32: no refinement needed
            if (u[jx + 2] >= v1) {
                // Only u[j+2] == v1 is possible; qhat = 2^32 - 1 and
                // rhat = u[j+1] + v1.
                qhat = ~uint32_t{0};
                uint64_t const r = uint64_t{u[jx + 1]} + v1;
                rhat_overflow = (r >> 32) != 0;
                rhat = static_cast<uint32_t>(r);
            }
            else {
                qhat = divlu32(u[jx + 2], u[jx + 1], v1, rhat);
            }
            while (!rhat_overflow &&
                   uint64_t{qhat} * v0 > ((uint64_t{rhat} << 32) | u[jx])) {
                --qhat;
                uint64_t const r = uint64_t{rhat} + v1;
                rhat_overflow = (r >> 32) != 0;
                rhat = static_cast<uint32_t>(r);
            }
            // u[j+2 .. j] -= qhat * (v1 : v0)
            uint64_t const p0 = uint64_t{qhat} * v0;
            uint64_t const p1 = uint64_t{qhat} * v1 + (p0 >> 32);
            uint32_t const p0_lo = static_cast<uint32_t>(p0);
            uint32_t const p1_lo = static_cast<uint32_t>(p1);
            uint32_t const p1_hi = static_cast<uint32_t>(p1 >> 32);
            uint32_t const b0 = u[jx] < p0_lo;
            u[jx] -= p0_lo;
            uint32_t const d1 = u[jx + 1] - p1_lo;
            uint32_t const b1 = (u[jx + 1] < p1_lo) | (d1 < b0);
            u[jx + 1] = d1 - b0;
            uint32_t const d2 = u[jx + 2] - p1_hi;
            uint32_t const b2 = (u[jx + 2] < p1_hi) | (d2 < b1);
            u[jx + 2] = d2 - b1;
            if (b2) {
                // qhat was one too large: add the divisor back.
                --qhat;
                uint64_t const s0 = uint64_t{u[jx]} + v0;
                u[jx] = static_cast<uint32_t>(s0);
                uint64_t const s1 = uint64_t{u[jx + 1]} + v1 + (s0 >> 32);
                u[jx + 1] = static_cast<uint32_t>(s1);
                u[jx + 2] += static_cast<uint32_t>(s1 >> 32);
            }
            q[jx] = qhat;
        }
        return {
            .quot = (uint64_t{q[1]} << 32) | q[0],
            .rem = ((uint64_t{u[1]} << 32) | u[0]) >> s};
#endif
    }

    [[gnu::always_inline]]
    constexpr void mulx(
        uint64_t const x, uint64_t const y, uint64_t &r_hi,
        uint64_t &r_lo) noexcept
    {
#ifdef __SIZEOF_INT128__
        using u128 = unsigned __int128;
        u128 const prod = static_cast<u128>(x) * static_cast<u128>(y);
        r_hi = static_cast<uint64_t>(prod >> u128{64});
        r_lo = static_cast<uint64_t>(prod);
#else
        // Schoolbook on 32-bit halves; each partial product is one
        // 32x32->64 multiply (mul + mulhu on rv32).
        uint64_t const x_lo = x & 0xffffffff;
        uint64_t const x_hi = x >> 32;
        uint64_t const y_lo = y & 0xffffffff;
        uint64_t const y_hi = y >> 32;
        uint64_t const p0 = x_lo * y_lo;
        uint64_t const p1 = x_lo * y_hi;
        uint64_t const p2 = x_hi * y_lo;
        uint64_t const p3 = x_hi * y_hi;
        uint64_t const mid =
            (p0 >> 32) + (p1 & 0xffffffff) + (p2 & 0xffffffff);
        r_lo = (mid << 32) | (p0 & 0xffffffff);
        r_hi = p3 + (p1 >> 32) + (p2 >> 32) + (mid >> 32);
#endif
    }

    template <size_t R, size_t M, size_t N>
    [[gnu::always_inline]]
    constexpr words_t<R>
    truncating_mul(words_t<M> const &x, words_t<N> const &y) noexcept
        requires(0 < R && R <= M + N)
    {
        words_t<R> result{0};
        for (size_t j = 0; j < N; j++) {
            uint64_t carry = 0;
            for (size_t i = 0; i < M && i + j < R; i++) {
                uint64_t hi;
                uint64_t lo;
                mulx(x[i], y[j], hi, lo);

                auto const [s0, c0] = addc(lo, result[i + j], false);
                auto const [s1, c1] = addc(s0, carry, false);
                result[i + j] = s1;
                auto const [s2, c2] = addc(hi, c0, c1);
                carry = s2;
            }
            if (j + M < R) {
                result[j + M] = carry;
            }
        }
        return result;
    }

}
