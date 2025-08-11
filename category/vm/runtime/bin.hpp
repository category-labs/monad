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

#include <category/vm/core/assert.h>

#include <algorithm>
#include <bit>
#include <cstdint>

namespace monad::vm::runtime
{
    /// Binary `N`-bit integer type with underlying type `std::uint32_t`
    template <std::size_t N>
        requires(N <= 32)
    class Bin
    {
    public:
        [[gnu::always_inline]]
        static constexpr Bin unsafe_from(std::uint32_t x) noexcept
        {
            return Bin(x);
        }

        static constexpr std::uint32_t upper =
            static_cast<std::uint32_t>(1ULL << N) - 1;

        [[gnu::always_inline]]
        static constexpr Bin max() noexcept
        {
            return Bin(upper);
        }

        [[gnu::always_inline]]
        constexpr Bin() noexcept
            : value_{0}
        {
        }

        template <std::size_t M>
            requires(N >= M)
        [[gnu::always_inline]]
        constexpr explicit(false) Bin(Bin<M> const &x) noexcept
            : value_{*x}
        {
        }

        template <std::size_t M>
            requires(N >= M)
        [[gnu::always_inline]]
        constexpr Bin &operator=(Bin<M> const &x) noexcept
        {
            value_ = *x;
            return *this;
        }

        [[gnu::always_inline]]
        constexpr std::uint32_t operator*() const noexcept
        {
            return value_;
        }

    private:
        [[gnu::always_inline]]
        constexpr explicit Bin(std::uint32_t x) noexcept
            : value_{x}
        {
            MONAD_VM_DEBUG_ASSERT(x < (1ULL << N));
        }

        std::uint32_t value_;
    };

    template <std::uint32_t x>
    static constexpr Bin<std::bit_width(x)> bin =
        Bin<std::bit_width(x)>::unsafe_from(x);

    template <std::size_t M, std::size_t N>
    [[gnu::always_inline]]
    constexpr Bin<std::max(M, N) + 1> operator+(Bin<M> x, Bin<N> y) noexcept
    {
        return Bin<std::max(M, N) + 1>::unsafe_from(*x + *y);
    }

    template <std::size_t M, std::size_t N>
    [[gnu::always_inline]]
    constexpr Bin<M + N> operator*(Bin<M> x, Bin<N> y) noexcept
    {
        return Bin<M + N>::unsafe_from(*x * *y);
    }

    template <std::uint32_t x, std::size_t N>
        requires(x < 32)
    [[gnu::always_inline]]
    constexpr Bin<N - x> shr(Bin<N> y) noexcept
    {
        return Bin<N - x>::unsafe_from(*y >> x);
    }

    template <std::uint32_t x, std::size_t N>
        requires(x < 32 && N < 32)
    [[gnu::always_inline]]
    constexpr Bin<std::max(size_t{x}, N) + 1 - x> shr_ceil(Bin<N> y) noexcept
    {
        return shr<x>(y + bin<Bin<x>::upper>);
    }

    template <std::uint32_t x, std::size_t N>
        requires(x < 32)
    [[gnu::always_inline]]
    constexpr Bin<N + x> shl(Bin<N> y) noexcept
    {
        return Bin<N + x>::unsafe_from(*y << x);
    }

    template <std::size_t M, std::size_t N>
    [[gnu::always_inline]]
    constexpr Bin<std::max(M, N)> max(Bin<M> x, Bin<N> y) noexcept
    {
        return Bin<std::max(M, N)>::unsafe_from(std::max(*x, *y));
    }

    template <std::size_t M, std::size_t N>
    [[gnu::always_inline]]
    constexpr Bin<std::min(M, N)> min(Bin<M> x, Bin<N> y) noexcept
    {
        return Bin<std::min(M, N)>::unsafe_from(std::min(*x, *y));
    }
};
