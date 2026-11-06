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

#include <category/core/monad_exception.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/jumpdest_scan.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <span>

#if defined(__AVX2__)
    #include <cstring>
    #include <immintrin.h>
#endif

using namespace monad::vm::compiler;

namespace monad::vm::interpreter
{
    Intercode::Intercode(std::span<uint8_t const> const code)
        : padded_code_(pad(code))
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code.size())))
        , jumpdest_map_(find_jumpdests(padded_code_, code.size()))
    {
    }

    Intercode::~Intercode()
    {
        delete[] (padded_code_ - start_padding_size);
    }

    uint8_t const *Intercode::pad(std::span<uint8_t const> const code)
    {
        MONAD_ASSERT_THROW(
            code.size() <= *code_size_t::max(),
            "Code size exceeds maximum representable value");

        auto *buffer =
            new uint8_t[start_padding_size + code.size() + end_padding_size];

        std::fill_n(&buffer[0], start_padding_size, 0);
        std::copy(code.begin(), code.end(), &buffer[start_padding_size]);
        std::fill_n(
            &buffer[code.size() + start_padding_size], end_padding_size, 0);

        return buffer + start_padding_size;
    }

    namespace detail
    {
        // PUSH immediates are skipped so a 0x5b inside one is not marked.
        void find_jumpdests_scalar(
            uint8_t const *const code, size_t const code_size,
            uint64_t *const bits)
        {
            for (size_t i = 0; i < code_size; ++i) {
                auto const op = code[i];
                if (op == EvmOpCode::JUMPDEST) {
                    bits[i >> 6] |= uint64_t{1} << (i & 63);
                }
                if (is_push_opcode(op)) {
                    i += get_push_opcode_index(op);
                }
            }
        }

#if defined(__AVX2__)
        // Adapted from evm2's SIMD jump-destination analysis, reimplemented
        // from Rust in C++:
        // https://github.com/danipopes/evm2
        // (crates/evm2/src/bytecode/analysis/x86.rs)
        // Copyright (c) 2026 DaniPopes
        // Licensed under the MIT license
        namespace
        {
            // Move each lane's position 2^k instructions forward unless that
            // would pass the lane. `nk` is the 2^k-step successor map.
            [[gnu::always_inline]] inline __m256i
            lift(__m256i const nk, __m256i const pos, __m256i const lane)
            {
                __m256i const q = _mm256_shuffle_epi8(nk, pos);
                __m256i const le =
                    _mm256_cmpeq_epi8(_mm256_max_epu8(q, lane), lane);
                return _mm256_blendv_epi8(pos, q, le);
            }

            [[gnu::always_inline]] inline __m256i square(__m256i const n)
            {
                return _mm256_max_epu8(_mm256_shuffle_epi8(n, n), n);
            }
        }

        // SIMD JUMPDEST analysis. Instead of the serial walk above, it
        // computes instruction boundaries 32 bytes at a time. Byte i of a
        // successor map holds 0x70 + (offset of the next instruction if one
        // started at i). Offsets 0..15 are 0x70..0x7f, which vpshufb indexes
        // by the low nibble; an offset >= 16 has bit 7 set, which vpshufb
        // maps to 0, so a hop chain stops at the block's first exit and an
        // out-of-block entry reads as a sign bit. Squaring the map by
        // shuffling it through itself composes 2, 4, 8 and 16 hops, and a
        // per-lane binary search from the block entry decides which bytes
        // start instructions. Each 256-bit register is two independent
        // 16-byte blocks (vpshufb stays within 128-bit halves); only the
        // entry offset carries between blocks.
        void find_jumpdests_avx2(
            uint8_t const *const code, size_t const code_size,
            uint64_t *const bits)
        {
            auto *const out = reinterpret_cast<uint8_t *>(bits);
            size_t const npairs = (code_size + 31) / 32;

            __m256i const len_floor = _mm256_set1_epi8(0x5f);
            // Signed max clamps every non-PUSH byte, 0x80..0xff included, to
            // 0x5f (PUSH0, zero immediate bytes), so n0[i] = 0x70 + i + 1 +
            // immediate length, with lane_bias[i] = 0x70 + 1 - 0x5f + i = 0x12
            // + i per 16-lane half. Each lane vector is that row repeated.
            // clang-format off
            __m256i const lane_bias = _mm256_setr_epi8(
                0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
                0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21,
                0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
                0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21);
            __m256i const lane = _mm256_setr_epi8(
                0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
                0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
                0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
                0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f);
            // clang-format on
            __m256i const jumpdest =
                _mm256_set1_epi8(static_cast<char>(EvmOpCode::JUMPDEST));
            __m256i const minus_one = _mm256_set1_epi8(-1);
            __m128i const sixteen = _mm_set1_epi8(16);

            __m128i entry = _mm_set1_epi8(0x70);

            for (size_t b = 0; b < npairs; ++b) {
                __m256i const op = _mm256_loadu_si256(
                    reinterpret_cast<__m256i const *>(code + 32 * b));
                __m256i const n0 =
                    _mm256_add_epi8(_mm256_max_epi8(op, len_floor), lane_bias);
                __m256i const n1 = square(n0);
                __m256i const n2 = square(n1);
                __m256i const n3 = square(n2);
                __m256i const n4 = square(n3);

                __m128i const n4_lo = _mm256_castsi256_si128(n4);
                __m128i const n4_hi = _mm256_extracti128_si256(n4, 1);
                __m128i const entry_hi = _mm_sub_epi8(
                    _mm_max_epu8(_mm_shuffle_epi8(n4_lo, entry), entry),
                    sixteen);
                __m128i const entry_next = _mm_sub_epi8(
                    _mm_max_epu8(_mm_shuffle_epi8(n4_hi, entry_hi), entry_hi),
                    sixteen);

                __m256i const entries = _mm256_set_m128i(entry_hi, entry);
                __m256i pos = entries;
                pos = lift(n3, pos, lane);
                pos = lift(n2, pos, lane);
                pos = lift(n1, pos, lane);
                __m256i const start = _mm256_or_si256(
                    _mm256_cmpeq_epi8(pos, lane),
                    _mm256_cmpeq_epi8(_mm256_shuffle_epi8(n0, pos), lane));
                // An entry past its block (inside a long PUSH) has its sign bit
                // set; such blocks contribute no instruction starts.
                __m256i const in_block = _mm256_cmpgt_epi8(entries, minus_one);
                __m256i const jd = _mm256_and_si256(
                    _mm256_and_si256(start, in_block),
                    _mm256_cmpeq_epi8(op, jumpdest));
                auto const mask =
                    static_cast<uint32_t>(_mm256_movemask_epi8(jd));
                std::memcpy(out + 4 * b, &mask, 4);

                entry = entry_next;
            }
        }
#endif
    }

    auto Intercode::find_jumpdests(uint8_t const *const code, size_t const n)
        -> JumpdestMap
    {
        auto jumpdests = JumpdestMap(detail::jumpdest_word_count(n), 0);
#if defined(__AVX2__)
        detail::find_jumpdests_avx2(code, n, jumpdests.data());
#else
        detail::find_jumpdests_scalar(code, n, jumpdests.data());
#endif
        return jumpdests;
    }
}
