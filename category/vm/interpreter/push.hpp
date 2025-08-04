#pragma once

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/stack.hpp>
#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.h>

#include <immintrin.h>

#include <cstdint>
#include <cstring>
#include <numeric>

namespace monad::vm::interpreter
{
    using enum compiler::EvmOpCode;

    namespace detail
    {
        consteval bool use_avx2_push(std::size_t const n) noexcept
        {
#ifdef __AVX2__
            return n > 0;
#else
            (void)n;
            return false;
#endif
        }

        using subword_t = runtime::uint256_t::word_type;

        // We need to do this memcpy dance to avoid triggering UB when
        // reading whole words from potentially unaligned addresses in the
        // instruction stream. The compilers seem able to optimise this out
        // effectively, and the generated code doesn't appear different to
        // the UB-triggering version.
        [[gnu::always_inline]] inline subword_t
        read_unaligned(std::uint8_t const *ptr)
        {
            alignas(subword_t) std::uint8_t aligned_mem[sizeof(subword_t)];
            std::memcpy(&aligned_mem[0], ptr, sizeof(subword_t));
            return std::byteswap(
                *reinterpret_cast<subword_t *>(&aligned_mem[0]));
        }

        template <std::size_t N, evmc_revision Rev>
            requires(!detail::use_avx2_push(N))
        [[gnu::always_inline]] inline void generic_push(
            runtime::Context &ctx, Intercode const &analysis,
            runtime::uint256_t const *stack_bottom,
            runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
            std::uint8_t const *instr_ptr)
        {
            static constexpr auto whole_words = N / 8;
            static constexpr auto leading_part = N % 8;

            check_requirements<PUSH0 + N, Rev>(
                ctx, analysis, stack_bottom, stack_top, gas_remaining);

            auto const leading_word = [instr_ptr] {
                auto word = subword_t{0};

                if constexpr (leading_part == 0) {
                    return word;
                }

                std::memcpy(
                    reinterpret_cast<std::uint8_t *>(&word) +
                        (8 - leading_part),
                    instr_ptr + 1,
                    leading_part);

                return std::byteswap(word);
            }();

            if constexpr (whole_words == 0) {
                interpreter::push(
                    stack_top, runtime::uint256_t{leading_word, 0, 0, 0});
            }
            else if constexpr (whole_words == 1) {
                interpreter::push(
                    stack_top,
                    runtime::uint256_t{
                        read_unaligned(instr_ptr + 1 + leading_part),
                        leading_word,
                        0,
                        0,
                    });
            }
            else if constexpr (whole_words == 2) {
                interpreter::push(
                    stack_top,
                    runtime::uint256_t{
                        read_unaligned(instr_ptr + 1 + 8 + leading_part),
                        read_unaligned(instr_ptr + 1 + leading_part),
                        leading_word,
                        0,
                    });
            }
            else if constexpr (whole_words == 3) {
                interpreter::push(
                    stack_top,
                    runtime::uint256_t{
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
                    runtime::uint256_t{
                        read_unaligned(instr_ptr + 1 + 24),
                        read_unaligned(instr_ptr + 1 + 16),
                        read_unaligned(instr_ptr + 1 + 8),
                        read_unaligned(instr_ptr + 1),
                    });
            }
        }

        template <std::size_t N, evmc_revision Rev>
            requires(detail::use_avx2_push(N))
        [[gnu::always_inline]] inline void avx2_push(
            runtime::Context &ctx, Intercode const &analysis,
            runtime::uint256_t const *stack_bottom,
            runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
            std::uint8_t const *instr_ptr)
        {
            static constexpr auto whole_words = N / 8;
            static constexpr auto leading_part = N % 8;

            check_requirements<PUSH0 + N, Rev>(
                ctx, analysis, stack_bottom, stack_top, gas_remaining);

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

    template <std::size_t N, evmc_revision Rev>
    struct push_impl
    {
        [[gnu::always_inline]] static inline void push(
            runtime::Context &ctx, Intercode const &analysis,
            runtime::uint256_t const *stack_bottom,
            runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
            std::uint8_t const *instr_ptr)
        {
            detail::generic_push<N, Rev>(
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr);
        }
    };

    template <evmc_revision Rev>
    struct push_impl<0, Rev>
    {
        [[gnu::always_inline]] static inline void push(
            runtime::Context &ctx, Intercode const &analysis,
            runtime::uint256_t const *stack_bottom,
            runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
            std::uint8_t const *)
        {
            check_requirements<PUSH0, Rev>(
                ctx, analysis, stack_bottom, stack_top, gas_remaining);
            interpreter::push(stack_top, 0);
        }
    };

    template <std::size_t N, evmc_revision Rev>
        requires(detail::use_avx2_push(N))
    struct push_impl<N, Rev>
    {
        [[gnu::always_inline]] static inline void push(
            runtime::Context &ctx, Intercode const &analysis,
            runtime::uint256_t const *stack_bottom,
            runtime::uint256_t *stack_top, std::int64_t &gas_remaining,
            std::uint8_t const *instr_ptr)
        {
            detail::avx2_push<N, Rev>(
                ctx,
                analysis,
                stack_bottom,
                stack_top,
                gas_remaining,
                instr_ptr);
        }
    };
}
