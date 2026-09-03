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

// Word-wise guest map hashes and a ZisK constant-load helper.

namespace monad::bits
{
    [[gnu::always_inline]] inline uint64_t load64(unsigned char const *const p) noexcept
    {
        uint64_t v;
        __builtin_memcpy(&v, p, 8);
        return v;
    }
    // Load constants on ZisK instead of rebuilding 64-bit immediates at each
    // inlined use. The memory operand forces a load; constant evaluation and
    // other targets keep the C++ value.
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
    // Addressable constants for the MurmurHash3 finalizer below.
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

    // Fold all 20 bytes. Overlapping bytes 12..15 occupy different bit
    // positions, so they do not cancel. ZisK uses the fold directly; SP1
    // adds fmix64. Maps compare full keys to resolve collisions.
    [[gnu::always_inline]] inline uint64_t hash_bytes20(unsigned char const *const p) noexcept
    {
        uint64_t const fold = load64(p) ^ load64(p + 8) ^ load64(p + 12);
#if defined(MONAD_ZKVM_ZISK)
        return fold;
#else
        return fmix64(fold);
#endif
    }

    // Mix the four words with one multiply and an XOR-shift on ZisK.
    // The shift brings high-bit differences down towards the low bits used
    // by immer's HAMT; multiplication alone cannot do that. SP1 uses fmix64.
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
