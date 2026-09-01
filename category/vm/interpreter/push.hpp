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

#include <category/core/runtime/uint256.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/stack.hpp>
#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>

#ifdef __AVX2__
    #include <immintrin.h>
#endif

#include <bit>
#include <cstdint>
#include <cstring>
#include <numeric>

namespace monad::vm::interpreter
{
    using enum compiler::EvmOpCode;

    namespace detail
    {
        consteval bool use_avx2_push(size_t const n) noexcept
        {
#ifdef __AVX2__
            return n > 0;
#else
            (void)n;
            return false;
#endif
        }

        using subword_t = uint256_t::word_type;

        // Assemble K big-endian bytes straight into a word. Going through a
        // little-endian load and a byte swap makes the word escape to the
        // stack on a target with no byte-swap instruction, which then pays a
        // reload plus the full mask-and-shift swap; shifting the bytes into
        // place costs K-1 ors and nothing else.
        template <size_t K>
        [[gnu::always_inline]] inline subword_t
        load_be_k(uint8_t const *const p) noexcept
        {
            static_assert(K >= 1 && K <= 8);
            return [p]<size_t... Is>(std::index_sequence<Is...>) {
                return ((static_cast<subword_t>(p[Is]) << (8 * (K - 1 - Is))) |
                        ...);
            }(std::make_index_sequence<K>{});
        }

        [[gnu::always_inline]] inline subword_t
        read_unaligned(uint8_t const *const ptr)
        {
            return load_be_k<8>(ptr);
        }

        // The caller checks. The gas and stack checks live in the handler, where
        // MONAD_VM_CHECK can tail-call Context::exit; reached from here they
        // could not, and the handler paid a stack frame for a call it never
        // makes -- see MONAD_VM_CHECK_AT in instruction_table.hpp.
        template <size_t N>
            requires(!detail::use_avx2_push(N))
        [[gnu::always_inline]] inline void generic_push(
            uint256_t *const stack_top, uint8_t const *const instr_ptr)
        {
            static constexpr auto whole_words = N / 8;
            static constexpr auto leading_part = N % 8;

            auto const leading_word = [instr_ptr] {
                if constexpr (leading_part == 0) {
                    return subword_t{0};
                }
                else {
                    return load_be_k<leading_part>(instr_ptr + 1);
                }
            }();

            if constexpr (whole_words == 0) {
                interpreter::push(stack_top, uint256_t{leading_word, 0, 0, 0});
            }
            else if constexpr (whole_words == 1) {
                interpreter::push(
                    stack_top,
                    uint256_t{
                        read_unaligned(instr_ptr + 1 + leading_part),
                        leading_word,
                        0,
                        0,
                    });
            }
            else if constexpr (whole_words == 2) {
                interpreter::push(
                    stack_top,
                    uint256_t{
                        read_unaligned(instr_ptr + 1 + 8 + leading_part),
                        read_unaligned(instr_ptr + 1 + leading_part),
                        leading_word,
                        0,
                    });
            }
            else if constexpr (whole_words == 3) {
                interpreter::push(
                    stack_top,
                    uint256_t{
                        read_unaligned(instr_ptr + 1 + 16 + leading_part),
                        read_unaligned(instr_ptr + 1 + 8 + leading_part),
                        read_unaligned(instr_ptr + 1 + leading_part),
                        leading_word,
                    });
            }
            else {
                static_assert(leading_part == 0);
                interpreter::push(
                    stack_top,
                    uint256_t{
                        read_unaligned(instr_ptr + 1 + 24),
                        read_unaligned(instr_ptr + 1 + 16),
                        read_unaligned(instr_ptr + 1 + 8),
                        read_unaligned(instr_ptr + 1),
                    });
            }
        }

        // The caller checks; see generic_push above.
        template <size_t N>
            requires(detail::use_avx2_push(N))
        [[gnu::always_inline]] inline void avx2_push(
            uint256_t *const stack_top, uint8_t const *const instr_ptr)
        {
            static constexpr auto whole_words = N / 8;
            static constexpr auto leading_part = N % 8;

            static constexpr int64_t m = ~(
                std::numeric_limits<int64_t>::max() >> (63 - leading_part * 8));

            // It is required that N > 0, otherwise we can index out of the
            // initial 30 bytes of padding to `instr_ptr`.
            static_assert(N > 0);
            __m256i y;

            if constexpr (N == 32) {
                std::memcpy(&y, instr_ptr + 1, 32);
            }
            else {
                std::memcpy(&y, instr_ptr - (31 - N), 32);
            }

            // y = {[y00...y07], [y10...y17], [y20...y27], [y30...y37]}
            y = _mm256_permute4x64_epi64(y, 27);
            // y = {[y30...y37], [y20...y27], [y10...y17], [y00...y07]}
            static constexpr int64_t s0 =
                0x0001020304050607LL | (whole_words == 0 ? m : 0);
            static constexpr int64_t s1 =
                0x08090a0b0c0d0e0fLL |
                (whole_words == 1 ? m : (whole_words < 1 ? -1 : 0));
            static constexpr int64_t s2 =
                0x0001020304050607LL |
                (whole_words == 2 ? m : (whole_words < 2 ? -1 : 0));
            static constexpr int64_t s3 =
                0x08090a0b0c0d0e0fLL |
                (whole_words == 3 ? m : (whole_words < 3 ? -1 : 0));
            y = _mm256_shuffle_epi8(y, _mm256_setr_epi64x(s0, s1, s2, s3));
            // For N = 32:
            // y = {[y37...y30], [y27...y20], [y17...y10], [y07...y00]}
            std::memcpy(reinterpret_cast<uint8_t *>(stack_top + 1), &y, 32);
        }
    }

    template <size_t N, Traits traits>
    struct push_impl
    {
        [[gnu::always_inline]] static inline void
        push(uint256_t *const stack_top, uint8_t const *const instr_ptr)
        {
            detail::generic_push<N>(stack_top, instr_ptr);
        }
    };

    template <Traits traits>
    struct push_impl<0, traits>
    {
        [[gnu::always_inline]] static inline void
        push(uint256_t *const stack_top, uint8_t const *)
        {
            interpreter::push(stack_top, 0);
        }
    };

    template <size_t N, Traits traits>
        requires(detail::use_avx2_push(N))
    struct push_impl<N, traits>
    {
        [[gnu::always_inline]] static inline void
        push(uint256_t *const stack_top, uint8_t const *const instr_ptr)
        {
            detail::avx2_push<N>(stack_top, instr_ptr);
        }
    };
}
