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

#if !defined(MONAD_ZKVM_ZISK)
    #include_next <category/core/runtime/uint256/overrides.hpp>
#else
    #include <category/core/likely.h>
    #include <category/core/runtime/uint256/intrinsics.hpp>

    #include <cstdint>

namespace monad::uint256::overrides
{
    inline constexpr bool enabled = true;

    // Stop at the first nonzero word instead of combining all four.
    template <typename U>
    [[gnu::always_inline]] constexpr bool is_nonzero(U const &x) noexcept
    {
        return x[0] != 0 || x[1] != 0 || x[2] != 0 || x[3] != 0;
    }

    // Compare high words first, stopping at the first difference. Treat high
    // differences as unlikely to favor the common path to the low word.
    template <typename U>
    [[gnu::always_inline]] constexpr bool
    less(U const &lhs, U const &rhs) noexcept
    {
        if (MONAD_UNLIKELY(lhs[3] != rhs[3])) {
            return lhs[3] < rhs[3];
        }
        if (MONAD_UNLIKELY(lhs[2] != rhs[2])) {
            return lhs[2] < rhs[2];
        }
        if (MONAD_UNLIKELY(lhs[1] != rhs[1])) {
            return lhs[1] < rhs[1];
        }
        return lhs[0] < rhs[0];
    }

    // Stop at the first difference. Check the low word first because small
    // integers differ there.
    template <typename U>
    [[gnu::always_inline]] constexpr bool equal(U const &x, U const &y) noexcept
    {
        if (x[0] != y[0]) {
            return false;
        }
        if (x[1] != y[1]) {
            return false;
        }
        if (x[2] != y[2]) {
            return false;
        }
        return x[3] == y[3];
    }

    template <typename U>
    [[gnu::always_inline]] constexpr bool slt(U const &x, U const &y) noexcept
    {
        auto const x_neg = x[U::num_words - 1] >> 63;
        auto const y_neg = y[U::num_words - 1] >> 63;
        // On ZisK, skip the full comparison when signs alone decide the result.
        if (x_neg != y_neg) {
            return x_neg != 0;
        }
        return x < y;
    }
}
#endif
