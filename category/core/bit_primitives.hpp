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

    // ── 64-bit constants ────────────────────────────────────────────────────────────────────
    // rv64 has no 64-bit immediate. gcc rebuilds one from lui/addi/slli/add — six or seven
    // instructions — at *every* site an inlining constant-user lands in, and the two consumers
    // below run 154,334 times per block between them (block 25551991: 112,425 fmix64, 41,909
    // popcount). Holding the constants in .rodata and loading them turns that into one shared
    // PC-relative address plus one load each: fmix64's hash_bytes20 assembles to 18 instructions
    // instead of 27, popcount64 to 19 instead of 29. An 8-aligned 8-byte load is 16 in the ZisK
    // cost model against 68 for each instruction it replaces.
    //
    // It has to be asm. gcc folds any constant it can see straight back into an immediate however
    // it is spelled, and the operand has to be "m" rather than "r" or gcc is free to satisfy the
    // address by rebuilding the value — the exact thing being removed.
    //
    // ZisK only. SP1 is rv32im, where a 64-bit constant is two 32-bit halves and materialising
    // costs about what loading would; the host keeps the plain literals. `if !consteval` keeps
    // the constant-evaluated path pure C++.
    [[gnu::always_inline]] inline constexpr uint64_t imm64(uint64_t const &k) noexcept
    {
#if defined(MONAD_ZKVM_ZISK)
        if !consteval {
            uint64_t v;
            asm("ld %0, %1" : "=r"(v) : "m"(k));
            return v;
        }
#endif
        return k;
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
    // ~~MEASURED CAVEAT: this one barely pays — 4.2 steps per call, 0.09 %.~~ That was true while
    // the four constants were immediates: materialising them cost about what libgcc's 29-instruction
    // helper did, so only the call was saved. Fetched (imm64 above) the body is 19 instructions, and
    // against the helper's 30 that is 684 COST per call — 41,909 calls, 28.7 M, 0.14 % of the block.
    // Still the strongest argument for asking the backend for `cpop`: one instruction would beat all
    // of this.
    alignas(8) inline constexpr uint64_t POPC_K[4] = {
        0x5555555555555555ull, 0x3333333333333333ull,
        0x0F0F0F0F0F0F0F0Full, 0x0101010101010101ull};

    [[gnu::always_inline]] inline constexpr int popcount64(uint64_t x) noexcept
    {
        // Not hoisted into a `const` local: gcc constant-evaluates a
        // const-initialised variable when it can, which takes `if !consteval`
        // down its false branch and folds the constant straight back into an
        // immediate. Written twice, the two asms CSE into one load.
        x = x - ((x >> 1) & imm64(POPC_K[0]));
        x = (x & imm64(POPC_K[1])) + ((x >> 2) & imm64(POPC_K[1]));
        x = (x + (x >> 4)) & imm64(POPC_K[2]);
        return static_cast<int>((x * imm64(POPC_K[3])) >> 56);
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

    // Exact zero-byte detector (Hacker's Delight): the returned word has 0x80
    // at every byte of x that is 0x00 and nothing anywhere else. The masked add
    // cannot carry across byte lanes (0x7f + 0x7f = 0xfe), which is what makes
    // it exact -- the shorter (x - lo) & ~x & hi form contaminates the lane
    // above a zero byte through its borrow.
    [[gnu::always_inline]] inline constexpr uint64_t
    zero_byte_mask(uint64_t const x) noexcept
    {
        constexpr uint64_t k7f = 0x7f7f7f7f7f7f7f7full;
        return ~((((x & k7f) + k7f) | x) | k7f);
    }

    // Number of 0x00 bytes in x: gather the 0x01 flags into the top byte.
    [[gnu::always_inline]] inline constexpr unsigned
    count_zero_bytes(uint64_t const x) noexcept
    {
        constexpr uint64_t k01 = 0x0101010101010101ull;
        return static_cast<unsigned>(((zero_byte_mask(x) >> 7) * k01) >> 56);
    }

    // Fixed-size 32-byte copy for KNOWN-aligned sources and arbitrary
    // destinations, inline. On rv32 (SP1) a 32-byte copy with unknown
    // destination alignment is a memcpy CALL (~18 cycles of overhead on a
    // ~60-cycle operation), and the guest pays it ~400 k times per block on
    // hash-reference writes and EVM memory staging. Head-align the
    // destination, then combine aligned source words; never reads or writes
    // outside [dst, dst+32) / [src, src+32).
    [[gnu::always_inline]] inline void
    copy32_from_aligned(unsigned char *d, unsigned char const *s) noexcept
    {
        using word = uintptr_t;
        constexpr size_t W = sizeof(word);
        size_t const head =
            (W - (reinterpret_cast<uintptr_t>(d) & (W - 1))) & (W - 1);
        for (size_t i = 0; i < head; ++i) {
            d[i] = s[i];
        }
        d += head;
        s += head;
        size_t const n = 32 - head;
        uintptr_t const mis = reinterpret_cast<uintptr_t>(s) & (W - 1);
        if (mis == 0) {
            for (size_t i = 0; i + W <= n; i += W) {
                *reinterpret_cast<word *>(d + i) =
                    *reinterpret_cast<word const *>(s + i);
            }
        }
        else {
            unsigned const rs = 8u * static_cast<unsigned>(mis);
            unsigned const ls = 8u * static_cast<unsigned>(W) - rs;
            auto const *sw = reinterpret_cast<word const *>(s - mis);
            word lo = *sw;
            size_t i = 0;
            for (; i + W <= n - (W - mis); i += W) {
                word const hi = *++sw;
                *reinterpret_cast<word *>(d + i) = (lo >> rs) | (hi << ls);
                lo = hi;
            }
            for (; i < n; ++i) {
                d[i] = s[i];
            }
        }
        size_t const tail = n & (W - 1);
        if (mis == 0) {
            for (size_t i = n - tail; i < n; ++i) {
                d[i] = s[i];
            }
        }
    }

    // Mirror: arbitrary source, WORD-ALIGNED destination (EVM memory loads
    // stage into an aligned local before the byte swap).
    [[gnu::always_inline]] inline void
    copy32_to_aligned(unsigned char *d, unsigned char const *s) noexcept
    {
        using word = uintptr_t;
        constexpr size_t W = sizeof(word);
        uintptr_t const mis = reinterpret_cast<uintptr_t>(s) & (W - 1);
        if (mis == 0) {
            for (size_t i = 0; i < 32; i += W) {
                *reinterpret_cast<word *>(d + i) =
                    *reinterpret_cast<word const *>(s + i);
            }
            return;
        }
        unsigned const rs = 8u * static_cast<unsigned>(mis);
        unsigned const ls = 8u * static_cast<unsigned>(W) - rs;
        auto const *sw = reinterpret_cast<word const *>(s - mis);
        word lo = *sw;
        size_t i = 0;
        // The last word would read past s + 32; finish it in bytes.
        for (; i + W <= 32 - (W - mis); i += W) {
            word const hi = *++sw;
            *reinterpret_cast<word *>(d + i) = (lo >> rs) | (hi << ls);
            lo = hi;
        }
        for (; i < 32; ++i) {
            d[i] = s[i];
        }
    }

    // Finalizer: murmur3's fmix64. Three xor-shifts and two multiplies, and the history is the
    // reason for every one of them. v1 (bare fold-and-multiply) measured 0.15 % SLOWER overall:
    // immer's HAMT indexes on the LOW bits and a multiply only carries upward. v2 added one
    // xor-shift (h ^= h >> 29) and turned the lever positive (+1.24 %) -- and still left the champ
    // 1.55x deeper than under wyhash, because for consecutive storage slots the varying byte sits
    // at the TOP of the last word and one shift only pushes that entropy down to about bit 27,
    // while the champ consumes 5-6 bits per level from the bottom. fmix64 finishes the avalanche.
    //
    // The state roots cannot validate any of this (a map is correct under any deterministic hash);
    // the step count is the only check, and it caught both earlier versions.

    // The two finalisation constants, as objects rather than literals -- see
    // imm64 at the top of this header.
    alignas(8) inline constexpr uint64_t FMIX_K[2] = {
        0xFF51AFD7ED558CCDull, 0xC4CEB9FE1A85EC53ull};

    [[gnu::always_inline]] inline constexpr uint64_t fmix64(uint64_t h) noexcept
    {
        h ^= h >> 33;
        h *= imm64(FMIX_K[0]);
        h ^= h >> 33;
        h *= imm64(FMIX_K[1]);
        h ^= h >> 33;
        return h;
    }

    [[gnu::always_inline]] inline uint64_t hash_bytes20(unsigned char const *const p) noexcept
    {
        return fmix64(load64(p) ^ load64(p + 8) ^ load64(p + 12));
    }

    [[gnu::always_inline]] inline uint64_t hash_bytes32(unsigned char const *const p) noexcept
    {
        return fmix64(load64(p) ^ load64(p + 8) ^ load64(p + 16) ^ load64(p + 24));
    }
}
