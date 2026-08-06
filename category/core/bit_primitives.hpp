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

#include <cstddef>
#include <cstdint>

// Bit primitives that must not become out-of-line calls in the zkVM guest.
//
// The guest targets riscv64ima. That base ISA has no rev8, cpop, clz or ctz — those live in the
// Zbb extension — so `std::byteswap`, `std::popcount` and `std::countl_zero` all lower to libgcc
// helpers, and the guest pays a call plus a multi-instruction body every time. Measured on the
// shipped guest, per block:
//
//     __bswapdi2       19.95 M steps   7.16 %   26-instruction body
//     __popcountdi2     1.29 M steps   0.46 %   29-instruction body
//     __clzdi2          1.18 M steps   0.42 %   45-instruction body
//
// The reth guest spends 0.01 % in ABI helpers in total: Rust's intrinsics stay inline. The
// asymmetry is a property of the toolchain and the target, not of either client.
//
// These replacements are bit-identical to the standard functions (each verified against the
// builtin over tens of millions of random inputs plus edge cases) and emit no call. They are not
// as good as the instruction would be — see the note on popcount — so the right long-term fix is
// for the backend to accept Zbb, at which point every one of these collapses to one instruction.
namespace monad::bits
{
    [[gnu::always_inline]] inline uint64_t load64(unsigned char const *const p) noexcept
    {
        uint64_t v;
        __builtin_memcpy(&v, p, 8);
        return v;
    }

    // ── byte order ──────────────────────────────────────────────────────────────────────────
    // Three rounds of mask-and-shift. The two 64-bit masks dominate the cost, so the sequence is
    // ~1.8x cheaper than the call only when several swaps share them — which is the uint256 case
    // (four words) that the EVM word path uses everywhere.

    [[gnu::always_inline]] inline constexpr uint64_t bswap64(uint64_t x) noexcept
    {
        x = ((x & 0x00FF00FF00FF00FFull) << 8) | ((x >> 8) & 0x00FF00FF00FF00FFull);
        x = ((x & 0x0000FFFF0000FFFFull) << 16) | ((x >> 16) & 0x0000FFFF0000FFFFull);
        return (x << 32) | (x >> 32);
    }

    [[gnu::always_inline]] inline constexpr uint32_t bswap32(uint32_t x) noexcept
    {
        x = ((x & 0x00FF00FFu) << 8) | ((x >> 8) & 0x00FF00FFu);
        return (x << 16) | (x >> 16);
    }

    [[gnu::always_inline]] inline constexpr uint16_t bswap16(uint16_t const x) noexcept
    {
        return static_cast<uint16_t>((x << 8) | (x >> 8));
    }

    template <typename T>
    [[gnu::always_inline]] inline constexpr T bswap(T const x) noexcept
    {
        if constexpr (sizeof(T) == 8) {
            return static_cast<T>(bswap64(static_cast<uint64_t>(x)));
        }
        else if constexpr (sizeof(T) == 4) {
            return static_cast<T>(bswap32(static_cast<uint32_t>(x)));
        }
        else if constexpr (sizeof(T) == 2) {
            return static_cast<T>(bswap16(static_cast<uint16_t>(x)));
        }
        else {
            return x;
        }
    }

    // ── count leading zeros ─────────────────────────────────────────────────────────────────
    // Same width semantics as std::countl_zero: the count is within sizeof(T)*8 bits and a zero
    // input returns that width. ~18 instructions against the helper's 45 plus the call.

    [[gnu::always_inline]] inline constexpr int clz64(uint64_t x) noexcept
    {
        if (x == 0) {
            return 64;
        }
        int n = 0;
        if (x <= 0x00000000FFFFFFFFull) { n += 32; x <<= 32; }
        if (x <= 0x0000FFFFFFFFFFFFull) { n += 16; x <<= 16; }
        if (x <= 0x00FFFFFFFFFFFFFFull) { n +=  8; x <<=  8; }
        if (x <= 0x0FFFFFFFFFFFFFFFull) { n +=  4; x <<=  4; }
        if (x <= 0x3FFFFFFFFFFFFFFFull) { n +=  2; x <<=  2; }
        if (x <= 0x7FFFFFFFFFFFFFFFull) { n +=  1; }
        return n;
    }

    template <typename T>
    [[gnu::always_inline]] inline constexpr int countl_zero(T const x) noexcept
    {
        constexpr int width = static_cast<int>(sizeof(T)) * 8;
        return clz64(static_cast<uint64_t>(x)) - (64 - width);
    }

    // ── population count ────────────────────────────────────────────────────────────────────
    // MEASURED CAVEAT: this one barely pays. Its four 64-bit constants take about six instructions
    // each to materialise, so the inline body costs nearly what the 29-instruction helper did and
    // only the call overhead is saved — 4.2 steps per call, 0.09 % of the guest. Kept because it
    // is free to keep, and recorded because it is the strongest argument for asking the backend
    // for `cpop`: no software sequence can compete when the constants alone cost more than a call.

    [[gnu::always_inline]] inline constexpr int popcount64(uint64_t x) noexcept
    {
        x = x - ((x >> 1) & 0x5555555555555555ull);
        x = (x & 0x3333333333333333ull) + ((x >> 2) & 0x3333333333333333ull);
        x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0Full;
        return static_cast<int>((x * 0x0101010101010101ull) >> 56);
    }

    template <typename T>
    [[gnu::always_inline]] inline constexpr int popcount(T const x) noexcept
    {
        return popcount64(static_cast<uint64_t>(x));
    }

    // ── hash-map keys ───────────────────────────────────────────────────────────────────────
    // Addresses and 32-byte words are keccak-derived or small big-endian integers, so folding the
    // 64-bit words and multiplying by the golden-ratio constant distributes them at least as well
    // as a byte-wise hash — and strictly better on consecutive storage slots.
    //
    // The final xor-shift is not optional. `immer`'s HAMT indexes on the LOW bits of the hash, and
    // a bare multiply leaves those nearly unmixed: without it this change measured 0.15 % SLOWER
    // overall and 2.8 % slower on the largest blocks, because the trie deepened. With it, +1.24 %.

    inline constexpr uint64_t GOLDEN = 0x9E3779B97F4A7C15ull;

    [[gnu::always_inline]] inline uint64_t hash_bytes20(unsigned char const *const p) noexcept
    {
        uint64_t const h = (load64(p) ^ load64(p + 8) ^ load64(p + 12)) * GOLDEN;
        return h ^ (h >> 29);
    }

    [[gnu::always_inline]] inline uint64_t hash_bytes32(unsigned char const *const p) noexcept
    {
        uint64_t const h =
            (load64(p) ^ load64(p + 8) ^ load64(p + 16) ^ load64(p + 24)) * GOLDEN;
        return h ^ (h >> 29);
    }
}
