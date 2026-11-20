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

    template <typename U, typename T>
    [[gnu::always_inline]] constexpr U
    shift_left(U const &x, T const shift_amount) noexcept
    {
        // Whole-word shifts need a separate path to avoid shifting by 64.
        auto const bit_shift = static_cast<unsigned>(shift_amount);
        unsigned const intra_word_shift = bit_shift & 63; // bit_shift % 64
        unsigned const cross_word_shift = 64 - intra_word_shift;
        auto const merge_left_words = [intra_word_shift, cross_word_shift](
                                          uint64_t const upper_word,
                                          uint64_t const lower_word) {
            return (upper_word << intra_word_shift) |
                   (lower_word >> cross_word_shift);
        };
        if (bit_shift < 128) {
            if (bit_shift < 64) {
                if (intra_word_shift == 0) {
                    return x; // bit_shift = 0
                }
                return U{
                    x[0] << intra_word_shift,
                    merge_left_words(x[1], x[0]),
                    merge_left_words(x[2], x[1]),
                    merge_left_words(x[3], x[2])};
            }
            if (intra_word_shift == 0) {
                return U{0, x[0], x[1], x[2]}; // bit_shift == 64
            }
            return U{
                0,
                x[0] << intra_word_shift,
                merge_left_words(x[1], x[0]),
                merge_left_words(x[2], x[1])};
        }
        if (bit_shift < 192) {
            if (intra_word_shift == 0) {
                return U{0, 0, x[0], x[1]}; // bit_shift == 128
            }
            return U{
                0, 0, x[0] << intra_word_shift, merge_left_words(x[1], x[0])};
        }
        return U{0, 0, 0, x[0] << intra_word_shift};
    }

    template <auto Type, typename U>
    [[gnu::always_inline]] constexpr U
    shift_right(U const &x, U const &shift_amount, uint64_t const fill) noexcept
    {
        // Keep whole-word shifts separate; top_word and fill preserve the sign.
        auto const bit_shift = static_cast<unsigned>(shift_amount[0]);
        unsigned const intra_word_shift = bit_shift & 63;
        unsigned const cross_word_shift = 64 - intra_word_shift;
        auto const merge_right_words = [intra_word_shift, cross_word_shift](
                                           uint64_t const upper_word,
                                           uint64_t const lower_word) {
            return (lower_word >> intra_word_shift) |
                   (upper_word << cross_word_shift);
        };
        uint64_t top_word;
        if constexpr (Type == U::RightShiftType::Logical) {
            top_word = x[3] >> intra_word_shift;
        }
        else {
            top_word = static_cast<uint64_t>(
                static_cast<int64_t>(x[3]) >> intra_word_shift);
        }
        if (bit_shift < 128) {
            if (bit_shift < 64) {
                if (intra_word_shift == 0) {
                    return x;
                }
                return U{
                    merge_right_words(x[1], x[0]),
                    merge_right_words(x[2], x[1]),
                    merge_right_words(x[3], x[2]),
                    top_word};
            }
            if (intra_word_shift == 0) {
                return U{x[1], x[2], x[3], fill};
            }
            return U{
                merge_right_words(x[2], x[1]),
                merge_right_words(x[3], x[2]),
                top_word,
                fill};
        }
        if (bit_shift < 192) {
            if (intra_word_shift == 0) {
                return U{x[2], x[3], fill, fill};
            }
            return U{merge_right_words(x[3], x[2]), top_word, fill, fill};
        }
        return U{top_word, fill, fill, fill};
    }

    template <typename U>
    [[gnu::always_inline]] constexpr U
    multiply(U const &lhs, U const &rhs) noexcept
    {
        if !consteval {
            // Gas and fee operands often fit in 64 bits; multiply just their
            // low words and keep the full 128-bit product.
            if ((lhs[1] | lhs[2] | lhs[3] | rhs[1] | rhs[2] | rhs[3]) == 0) {
                uint64_t hi;
                uint64_t lo;
                intrinsics::mulx(lhs[0], rhs[0], hi, lo);
                return U{lo, hi, 0, 0};
            }
        }
        return truncating_mul(lhs, rhs);
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
