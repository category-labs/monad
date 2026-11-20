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
    #include <category/core/assert.h>
    #include <category/core/likely.h>
    #include <category/core/runtime/uint256/intrinsics.hpp>

    #include <bit>
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

    // Compare two 8-byte-aligned 32-byte blocks via ZisK DMA.
    // On CSR 0x814, ZisK's transpiler reads the immediately following addi
    // for the second pointer and length, emitting one comparison for the pair.
    // One asm block prevents the compiler from inserting code between them.
    [[gnu::always_inline]] inline bool
    zisk_equal32(uint64_t const *const a, uint64_t const *const b) noexcept
    {
        uint64_t differ;
        // Enable CSR instructions locally, then restore the assembler options.
        asm(".option push\n\t"
            ".option arch, +zicsr\n\t"
            // DMA comparison (0x814): a (%1) in, difference flag (%0) out.
            "csrrs %0, 0x814, %1\n\t"
            // Metadata for ZisK: b (%2), length 32; no b + 32 is computed.
            "addi x0, %2, 32\n\t"
            ".option pop"
            // %0: register output; '&' prevents overlap with input registers.
            : "=&r"(differ)
            : "r"(a), // %1
              "r"(b), // %2
              // Declare both 32-byte reads so the compiler preserves their
              // data.
              "m"(*reinterpret_cast<uint64_t const(*)[4]>(a)),
              "m"(*reinterpret_cast<uint64_t const(*)[4]>(b)));
        return differ == 0; // Zero means all 32 bytes match.
    }

    // arith256 computes a*b+c as a low and a high 256-bit result.
    struct DivisionProductParams
    {
        uint64_t const *a;
        uint64_t const *b;
        uint64_t const *c;
        uint64_t *low;
        uint64_t *high;
    };

    // Verify that q·v + r == u in 512 bits and r < v (requires v != 0).
    template <typename U>
    [[gnu::always_inline]] inline div_result<U> verify_division_hint(
        U const &u, U const &v, uint64_t const (&qr)[8]) noexcept
    {
        alignas(8) uint64_t d[8]; // q·v + r, low half then high half
        DivisionProductParams p{
            qr, reinterpret_cast<uint64_t const *>(&v), qr + 4, d, d + 4};
        asm volatile(".option push\n\t"
                     ".option arch, +zicsr\n\t"
                     "csrs 0x801, %0\n\t"
                     ".option pop"
                     :
                     : "r"(&p)
                     : "memory");
        U const q{qr[0], qr[1], qr[2], qr[3]};
        U const r{qr[4], qr[5], qr[6], qr[7]};
        alignas(8) constexpr uint64_t zero_words[4]{};
        MONAD_ASSERT(
            zisk_equal32(d, reinterpret_cast<uint64_t const *>(&u)) &&
            zisk_equal32(d + 4, zero_words));
        MONAD_ASSERT(r < v);
        return {.quot = q, .rem = r};
    }

    // Call fcall 19 directly to avoid div_rem256_c's copies and
    // zero-initialisation.
    template <typename U>
    [[gnu::always_inline]] inline div_result<U>
    hinted_division(U const &u, U const &v) noexcept
    {
        static_assert(alignof(U) >= 8);
        static_assert(sizeof(U) == 4 * sizeof(uint64_t));
        alignas(8) uint64_t qr[8]; // the quotient, then the remainder
        asm volatile(".option push\n\t"
                     ".option arch, +zicsr\n\t"
                     "csrs 0x8F2, %[u]\n\t" // a parameter: the four words at u
                     "csrs 0x8F2, %[v]\n\t"
                     "csrwi 0x8C0, 19\n\t" // FCALL_UINT256_DIV_ID
                     "csrs 0x815, %[qr]\n\t" // inputcpy: the eight result words
                     "addi x0, %[qr], 64\n\t"
                     ".option pop"
                     :
                     : [u] "r"(&u), [v] "r"(&v), [qr] "r"(qr)
                     : "memory");
        return verify_division_hint(u, v, qr);
    }

    // The caller handles zero divisors and constant evaluation.
    template <typename U>
    [[gnu::always_inline]] inline div_result<U>
    divide(U const &u, U const &v) noexcept
    {
        uint64_t const v_high = v[1] | v[2] | v[3];
        // For v = 2^k, a shift and mask replace the division hint and its
        // verification. Check the low word first to quickly reject common
        // divisors with multiple set bits (e.g. decimal scales).
        if ((v[0] & (v[0] - 1)) == 0) {
            unsigned k = 256; // no single bit found
            if (v[0] != 0) {
                if (v_high == 0) {
                    k = static_cast<unsigned>(std::countr_zero(v[0]));
                }
            }
            else if (v[1] != 0) {
                if ((v[1] & (v[1] - 1)) == 0 && (v[2] | v[3]) == 0) {
                    k = 64 + static_cast<unsigned>(std::countr_zero(v[1]));
                }
            }
            else if (v[2] != 0) {
                if ((v[2] & (v[2] - 1)) == 0 && v[3] == 0) {
                    k = 128 + static_cast<unsigned>(std::countr_zero(v[2]));
                }
            }
            else if ((v[3] & (v[3] - 1)) == 0) {
                k = 192 + static_cast<unsigned>(std::countr_zero(v[3]));
            }
            if (k < 256) {
                return {.quot = u >> U{k}, .rem = u & (v - 1)};
            }
        }
        // For 64-bit operands, use native division instead of the hint.
        if ((u[1] | u[2] | u[3] | v_high) == 0) {
            return {.quot = U{u[0] / v[0]}, .rem = U{u[0] % v[0]}};
        }
        // Read operands in place; keep results separate for x /= x.
        return hinted_division(u, v);
    }

}

// Preserve the shared DMA helper used by the interpreter.
namespace monad
{
    using uint256::overrides::zisk_equal32;
}
#endif
