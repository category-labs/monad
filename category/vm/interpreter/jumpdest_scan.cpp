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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/jumpdest_scan.hpp>

#include <cstddef>
#include <cstdint>

#if defined(__AVX2__)
    #include <cstring>
    #include <immintrin.h>
#endif

using namespace monad::vm::compiler;

namespace monad::vm::interpreter::detail
{
    // No EIP-8024 (DUPN/SWAPN/EXCHANGE) case: an allowed immediate is never
    // JUMPDEST or PUSH1-32, and a disallowed one is not an immediate.

    void find_jumpdests_scalar(
        uint8_t const *const code, size_t const code_size, uint64_t *const bits)
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
    // Adapted from evm2's SIMD jump-destination analysis, reimplemented from
    // Rust in C++, and used under its MIT license:
    // https://github.com/alloy-rs/evm2
    // (crates/evm2/src/bytecode/analysis/x86.rs)
    //
    // Copyright (c) 2026 DaniPopes
    //
    // Permission is hereby granted, free of charge, to any person obtaining a
    // copy of this software and associated documentation files (the
    // "Software"), to deal in the Software without restriction, including
    // without limitation the rights to use, copy, modify, merge, publish,
    // distribute, sublicense, and/or sell copies of the Software, and to
    // permit persons to whom the Software is furnished to do so, subject to
    // the following conditions:
    //
    // The above copyright notice and this permission notice shall be included
    // in all copies or substantial portions of the Software.
    //
    // THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
    // OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    // MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
    // IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
    // CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
    // TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
    // SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
    //
    // Changes from upstream:
    // - AVX2 only, with no fast paths for pairs without PUSH or JUMPDEST bytes,
    //   so the cost does not depend on the bytecode.
    // - Scans the partial last pair with SIMD over zero padding instead of
    //   finishing with a scalar walk.
    // - Copies the code into `dst` as it scans.
    // - Computes the next pair's maps before finishing the current one.
    // - The binary search selects with a subtract instead of a min and a
    //   compare, and out-of-block lanes are cleared with andnot before the
    //   movemask.

    // SIMD JUMPDEST analysis: computes instruction boundaries 32 bytes at
    // a time. Byte i of a successor map holds 0x70 + (offset of the next
    // instruction if one started at i). Offsets 0..15 are 0x70..0x7f,
    // which vpshufb indexes by the low nibble; an offset >= 16 has bit 7
    // set, which vpshufb maps to 0, so a hop chain stops at the block's
    // first exit and an out-of-block entry reads as a sign bit. Squaring
    // the map by shuffling it through itself composes 2, 4, 8 and 16
    // hops, and a per-lane binary search from the block entry decides
    // which bytes start instructions. Each 256-bit register is two
    // independent 16-byte blocks (vpshufb stays within 128-bit halves);
    // only the entry offset carries between blocks.
    namespace
    {
        // Move each lane's position 2^k instructions forward unless that
        // would pass the lane. `nk` is the 2^k-step successor map.
        [[gnu::always_inline]] inline __m256i
        lift(__m256i const nk, __m256i const pos, __m256i const lane)
        {
            __m256i const q = _mm256_shuffle_epi8(nk, pos);
            // q is zero or an encoded successor in [0x71, 0xa0].
            // lane is in [0x70, 0x7f], so lane - q fits a signed byte.
            // Its sign bit selects pos precisely when q > lane.
            __m256i const gt = _mm256_sub_epi8(lane, q);
            return _mm256_blendv_epi8(q, pos, gt);
        }

        [[gnu::always_inline]] inline __m256i square(__m256i const n)
        {
            return _mm256_max_epu8(_mm256_shuffle_epi8(n, n), n);
        }

        struct ScanConstants
        {
            __m256i len_floor = _mm256_set1_epi8(0x5f);
            // Signed max clamps every non-PUSH byte, 0x80..0xff included,
            // to 0x5f (PUSH0, zero immediate bytes), so
            // n0[i] = 0x70 + i + 1 + immediate length, with
            // lane_bias[i] = 0x70 + 1 - 0x5f + i = 0x12 + i per 16-lane
            // half. Each lane vector is that row repeated.
            // clang-format off
            __m256i lane_bias = _mm256_setr_epi8(
                0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
                0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21,
                0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
                0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x21);
            __m256i lane = _mm256_setr_epi8(
                0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
                0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
                0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,
                0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f);
            // clang-format on
            __m256i jumpdest =
                _mm256_set1_epi8(static_cast<char>(EvmOpCode::JUMPDEST));
            __m128i sixteen = _mm_set1_epi8(16);
        };

        // Two 16-byte blocks' opcodes and successor maps: n0 is one hop,
        // n1..n4 are 2, 4, 8 and 16 hops.
        struct BlockPair
        {
            __m256i op;
            __m256i n0;
            __m256i n1;
            __m256i n2;
            __m256i n3;
            __m256i n4;
        };

        [[gnu::always_inline]] inline BlockPair
        load_pair(ScanConstants const &k, uint8_t const *const p)
        {
            BlockPair pair;
            pair.op =
                _mm256_loadu_si256(reinterpret_cast<__m256i_u const *>(p));
            pair.n0 = _mm256_add_epi8(
                _mm256_max_epi8(pair.op, k.len_floor), k.lane_bias);
            pair.n1 = square(pair.n0);
            pair.n2 = square(pair.n1);
            pair.n3 = square(pair.n2);
            pair.n4 = square(pair.n3);
            return pair;
        }

        // The pair's JUMPDEST bits, given the entry offset carried from
        // the previous pair; advances `entry` past this pair.
        [[gnu::always_inline]] inline uint32_t jumpdest_mask(
            ScanConstants const &k, BlockPair const &pair, __m128i &entry)
        {
            __m128i const n4_lo = _mm256_castsi256_si128(pair.n4);
            __m128i const n4_hi = _mm256_extracti128_si256(pair.n4, 1);
            __m128i const entry_hi = _mm_sub_epi8(
                _mm_max_epu8(_mm_shuffle_epi8(n4_lo, entry), entry), k.sixteen);
            __m128i const entry_next = _mm_sub_epi8(
                _mm_max_epu8(_mm_shuffle_epi8(n4_hi, entry_hi), entry_hi),
                k.sixteen);

            __m256i const entries = _mm256_set_m128i(entry_hi, entry);
            __m256i pos = entries;
            pos = lift(pair.n3, pos, k.lane);
            pos = lift(pair.n2, pos, k.lane);
            pos = lift(pair.n1, pos, k.lane);
            __m256i const start = _mm256_or_si256(
                _mm256_cmpeq_epi8(pos, k.lane),
                _mm256_cmpeq_epi8(_mm256_shuffle_epi8(pair.n0, pos), k.lane));
            // An entry past its block (inside a long PUSH) has its sign bit
            // set; such blocks contribute no instruction starts. movemask
            // reads only sign bits, so andnot with `entries` drops them.
            __m256i const jd = _mm256_and_si256(
                _mm256_andnot_si256(entries, start),
                _mm256_cmpeq_epi8(pair.op, k.jumpdest));

            entry = entry_next;
            return static_cast<uint32_t>(_mm256_movemask_epi8(jd));
        }
    }

    void copy_and_find_jumpdests_avx2(
        uint8_t const *const src, uint8_t *const dst, size_t const code_size,
        uint64_t *const bits)
    {
        auto *const out = reinterpret_cast<uint8_t *>(bits);
        size_t const npairs = (code_size + 31) / 32;
        size_t const whole = code_size / 32;
        // The partial last pair is copied first and scanned from `dst`,
        // where padding follows it, so `src` is never read past its end.
        if (code_size > 32 * whole) {
            std::memcpy(
                dst + 32 * whole, src + 32 * whole, code_size - 32 * whole);
        }
        if (npairs == 0) {
            return;
        }
        auto const pair_at = [&](size_t const b) -> uint8_t const * {
            if (b >= whole) {
                return dst + 32 * b;
            }
            return src + 32 * b;
        };
        ScanConstants const k;
        __m128i entry = _mm_set1_epi8(0x70);

        // Loading the next pair before finishing this one lets the core
        // overlap the two pairs' long dependency chains.
        BlockPair pair = load_pair(k, pair_at(0));
        for (size_t b = 0; b + 1 < npairs; ++b) {
            BlockPair const next = load_pair(k, pair_at(b + 1));
            // Only the last pair can be partial.
            _mm256_storeu_si256(
                reinterpret_cast<__m256i_u *>(dst + 32 * b), pair.op);
            uint32_t const mask = jumpdest_mask(k, pair, entry);
            std::memcpy(out + 4 * b, &mask, 4);
            pair = next;
        }
        if (npairs == whole) {
            _mm256_storeu_si256(
                reinterpret_cast<__m256i_u *>(dst + 32 * (npairs - 1)),
                pair.op);
        }
        uint32_t const mask = jumpdest_mask(k, pair, entry);
        std::memcpy(out + 4 * (npairs - 1), &mask, 4);
    }
#endif
}
