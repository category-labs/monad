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

#include <category/core/config.hpp>

#include <cstdint>

// Guest map hashes seeded from the block hash before populating maps.
// Changing transactions or header fields changes the public seed, limiting
// reuse of precomputed collisions. The computed state root must match the
// header before this hash is published.

MONAD_NAMESPACE_BEGIN

namespace bits
{
    [[gnu::always_inline]] inline uint64_t
    load64(unsigned char const *const p) noexcept
    {
        uint64_t v;
        __builtin_memcpy(&v, p, 8);
        return v;
    }

    [[gnu::always_inline]] inline uint64_t
    load32(unsigned char const *const p) noexcept
    {
        uint32_t v;
        __builtin_memcpy(&v, p, 4);
        return v;
    }

    // Public hash parameters shared by the guest maps. Each block derives
    // its own values from the block hash, limiting reuse of precomputed
    // collision sets across blocks.
    alignas(8) inline uint64_t map_keys[4] = {
        // Blowfish defaults, replaced by set_map_keys for each block.
        0x243F6A8885A308D3ull,
        0x13198A2E03707344ull,
        0xA4093822299F31D0ull,
        0x082EFA98EC4E6C89ull};

    // Replace all four parameters with the block hash's 64-bit words.
    // Call before populating maps; changing keys invalidates existing lookups.
    inline void set_map_keys(unsigned char const (&digest)[32]) noexcept
    {
        for (int i = 0; i < 4; ++i) {
            map_keys[i] = load64(digest + 8 * i);
        }
        // An odd multiplier preserves distinct tails for a fixed prefix.
        map_keys[3] |= 1;
    }

    // Fold a 128-bit product to 64 bits. Mix words before combining them
    // to avoid the old XOR fold's pairwise cancellation.
    [[gnu::always_inline]] inline uint64_t
    mum(uint64_t const a, uint64_t const b) noexcept
    {
        unsigned __int128 const r = static_cast<unsigned __int128>(a) * b;
        return static_cast<uint64_t>(r) ^ static_cast<uint64_t>(r >> 64);
    }

    [[gnu::always_inline]] inline uint64_t
    hash_bytes20(unsigned char const *const p) noexcept
    {
        return mum(load64(p) ^ map_keys[0], load64(p + 8) ^ map_keys[1]) +
               (load32(p + 16) ^ map_keys[2]) * map_keys[3];
    }

    [[gnu::always_inline]] inline uint64_t
    hash_bytes32(unsigned char const *const p) noexcept
    {
        return mum(load64(p) ^ map_keys[0], load64(p + 8) ^ map_keys[1]) ^
               mum(load64(p + 16) ^ map_keys[2], load64(p + 24) ^ map_keys[3]);
    }
}

MONAD_NAMESPACE_END
