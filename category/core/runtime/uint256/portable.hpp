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

#include <cstddef>
#include <cstdint>

// This header file provides constexpr-compatible C++ implementations of the
// binary operations (add, minus, times, division, left shift, and right shift)
// used by the uint256 implementation,

MONAD_NAMESPACE_BEGIN

[[gnu::always_inline]]
constexpr inline result_with_carry<uint64_t>
addc(uint64_t const lhs, uint64_t const rhs, bool const carry_in) noexcept;

[[gnu::always_inline]]
inline constexpr void mulx(
    uint64_t const x, uint64_t const y, uint64_t &r_hi,
    uint64_t &r_lo) noexcept;

MONAD_NAMESPACE_END

namespace monad::uint256::portable
{

    [[gnu::always_inline]]
    constexpr inline result_with_carry<uint64_t>
    addc(uint64_t const lhs, uint64_t const rhs, bool const carry_in) noexcept
    {
        uint64_t const sum = lhs + rhs;
        bool carry_out = sum < lhs;
        uint64_t const sum_carry = sum + carry_in;
        carry_out |= sum_carry < sum;
        return result_with_carry{.value = sum_carry, .carry = carry_out};
    }

    [[gnu::always_inline]] constexpr inline result_with_carry<uint64_t>
    subb(uint64_t const lhs, uint64_t const rhs, bool const borrow_in) noexcept
    {
        uint64_t const sub = lhs - rhs;
        bool borrow_out = rhs > lhs;
        uint64_t const sub_borrow = sub - borrow_in;
        borrow_out |= borrow_in > sub;
        return result_with_carry{.value = sub_borrow, .carry = borrow_out};
    }

    [[gnu::always_inline]]
    inline constexpr uint64_t
    shld(uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        return (high << shift) | ((low >> 1) >> (63 - shift));
    }

    [[gnu::always_inline]]
    inline constexpr uint64_t
    shrd(uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        return (low >> shift) | ((high << 1) << (63 - shift));
    }

    [[gnu::always_inline]]
    constexpr inline div_result<uint64_t>
    div(uint64_t u_hi, uint64_t u_lo, uint64_t const v) noexcept
    {
        using u128 = unsigned __int128;
        auto const u = static_cast<u128>(uint128_t{u_lo, u_hi});
        auto const quot = static_cast<uint64_t>(u / v);
        auto const rem = static_cast<uint64_t>(u % v);
        return {.quot = quot, .rem = rem};
    }

    [[gnu::always_inline]]
    inline constexpr void mulx(
        uint64_t const x, uint64_t const y, uint64_t &r_hi,
        uint64_t &r_lo) noexcept
    {
        using u128 = unsigned __int128;
        u128 const prod = static_cast<u128>(x) * static_cast<u128>(y);
        r_hi = static_cast<uint64_t>(prod >> u128{64});
        r_lo = static_cast<uint64_t>(prod);
    }

    template <size_t R, size_t M, size_t N>
    [[gnu::always_inline]]
    inline constexpr words_t<R>
    truncating_mul(words_t<M> const &x, words_t<N> const &y) noexcept
        requires(0 < R && R <= M + N)
    {
        words_t<R> result{0};
        for (size_t j = 0; j < N; j++) {
            uint64_t carry = 0;
            for (size_t i = 0; i < M && i + j < R; i++) {
                uint64_t hi;
                uint64_t lo;
                monad::mulx(x[i], y[j], hi, lo);

                auto const [s0, c0] = monad::addc(lo, result[i + j], false);
                auto const [s1, c1] = monad::addc(s0, carry, false);
                result[i + j] = s1;
                auto const [s2, c2] = monad::addc(hi, c0, c1);
                carry = s2;
            }
            if (j + M < R) {
                result[j + M] = carry;
            }
        }
        return result;
    }

}
