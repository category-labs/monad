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

#include <cstdint>

// Hash-map key hashing for the zkVM guest, and the 64-bit-constant load it rests on.
//
// The guest builds -march=rv64ima_zicsr_zbb_zbs_zbkb, so rev8, clz, ctz and cpop are single
// instructions and std::byteswap / std::countl_zero / std::popcount reach them directly. The
// software fallbacks that once lived here for a bare rv64ima build are therefore not carried:
// under Zbb gcc never goes through them, and -ffunction-sections plus gc-sections drops them
// from the ELF. What remains is what the flag does not provide.

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
    // ── hash-map keys ───────────────────────────────────────────────────────────────────────
    // Addresses and 32-byte words are keccak-derived or small big-endian integers, so folding the
    // 64-bit words and multiplying by the golden-ratio constant distributes them at least as well
    // as a byte-wise hash — and strictly better on consecutive storage slots.
    //
    // The final xor-shift is not optional. `immer`'s HAMT indexes on the LOW bits of the hash, and
    // a bare multiply leaves those nearly unmixed: without it this change measured 0.15 % SLOWER
    // overall and 2.8 % slower on the largest blocks, because the trie deepened. With it, +1.24 %.

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

    // The fold covers all twenty bytes: the second and third loads overlap on
    // bytes 12-15, but at opposite ends of their words, so nothing cancels.
    //
    // On the guest the fold is the whole hash. Its only caller hashes an
    // Address, and an address is the low twenty bytes of a keccak digest --
    // of a public key, of (sender, nonce), or of a CREATE2 preimage -- so
    // every bit of it is already uniform and an avalanche has nothing left to
    // spread. fmix64 is ten instructions and two of them are multiplies, which
    // ZisK prices at 97 cells against 15 for an add.
    //
    // Distribution is the only thing at risk, and it is not a correctness
    // risk: the map compares keys, so a worse hash shows up as probes and
    // never as a wrong answer.
    [[gnu::always_inline]] inline uint64_t hash_bytes20(unsigned char const *const p) noexcept
    {
        uint64_t const fold = load64(p) ^ load64(p + 8) ^ load64(p + 12);
#if defined(MONAD_ZKVM_ZISK)
        return fold;
#else
        return fmix64(fold);
#endif
    }

    // One multiply, not fmix64's two. The section comment above states the
    // design this restores -- fold the words, multiply by the golden-ratio
    // constant, and keep the final xor-shift, which is NOT optional because
    // immer's HAMT indexes on the LOW bits and a bare multiply leaves those
    // nearly unmixed. fmix64 spends a second multiply, at 97 cells against 15
    // for an add, on entropy the first one has already spread.
    //
    // Unlike hash_bytes20 this keeps a mixing step: an address goes only to
    // unordered_dense, which buckets on the high bits, while a 32-byte word
    // reaches the page map as well.
    [[gnu::always_inline]] inline uint64_t hash_bytes32(unsigned char const *const p) noexcept
    {
        uint64_t const fold =
            load64(p) ^ load64(p + 8) ^ load64(p + 16) ^ load64(p + 24);
#if defined(MONAD_ZKVM_ZISK)
        alignas(8) static constexpr uint64_t GOLDEN = 0x9E3779B97F4A7C15ull;
        uint64_t const h = fold * imm64(GOLDEN);
        return h ^ (h >> 29);
#else
        return fmix64(fold);
#endif
    }
}
