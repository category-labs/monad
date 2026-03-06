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

extern "C"
{
#include <blake3_impl.h>
}

#include <category/execution/monad/db/storage_page.hpp>

#include <bit>
#include <cstring>

MONAD_NAMESPACE_BEGIN

// ── BLAKE3 page commitment
// ────────────────────────────────────────────────────
//
// Binary Merkle tree over a storage page using BLAKE3 compress.
//
//   64 pair-leaves  →  32  →  16  →  8  →  4  →  2  →  root
//
// Leaves are domain-separated from parents via a derived IV.

namespace
{
    constexpr size_t NUM_LEAVES = storage_page_t::SLOTS / 2;
    constexpr uint8_t PARENT_FLAGS = CHUNK_START | CHUNK_END;
    constexpr char DOMAIN_KEY[] = "ultra_merkle_pair_leaf_domain___";
    static_assert(sizeof(DOMAIN_KEY) - 1 == 32);

    // Hash `n` 64-byte blocks into `n` 32-byte chaining values.
    void hash_level(
        uint8_t const *data, size_t const n, uint32_t const key[8],
        uint8_t const flags, uint8_t *out)
    {
        uint8_t const *inputs[NUM_LEAVES];
        for (size_t i = 0; i < n; ++i) {
            inputs[i] = data + i * BLAKE3_BLOCK_LEN;
        }
        blake3_hash_many(inputs, n, 1, key, 0, false, flags, 0, 0, out);
    }

} // namespace

bytes32_t page_commit(storage_page_t const &page)
{
    static_assert(std::has_single_bit(NUM_LEAVES));

    // Derive leaf IV from domain key (cached across calls).
    static uint32_t const *leaf_iv = [] {
        static uint32_t iv[8];
        uint8_t block[BLAKE3_BLOCK_LEN] = {};
        std::memcpy(block, DOMAIN_KEY, sizeof(DOMAIN_KEY) - 1);
        std::memcpy(iv, IV, sizeof(iv));
        blake3_compress_in_place(
            iv, block, BLAKE3_BLOCK_LEN, 0, DERIVE_KEY_MATERIAL);
        return iv;
    }();

    auto const *raw = page.slots[0].bytes;
    alignas(32) uint8_t l0[64 * BLAKE3_OUT_LEN];
    alignas(32) uint8_t l1[32 * BLAKE3_OUT_LEN];
    alignas(32) uint8_t l2[16 * BLAKE3_OUT_LEN];
    alignas(32) uint8_t l3[8 * BLAKE3_OUT_LEN];
    alignas(32) uint8_t l4[4 * BLAKE3_OUT_LEN];
    alignas(32) uint8_t l5[2 * BLAKE3_OUT_LEN];

    // Level 0: 64 pair-leaves (each 64 bytes = 2 adjacent slots)
    hash_level(raw, 64, leaf_iv, DERIVE_KEY_MATERIAL, l0);

    // Level 1: 64 → 32
    hash_level(l0, 32, IV, PARENT_FLAGS, l1);

    // Level 2: 32 → 16
    hash_level(l1, 16, IV, PARENT_FLAGS, l2);

    // Level 3: 16 → 8
    hash_level(l2, 8, IV, PARENT_FLAGS, l3);

    // Level 4: 8 → 4
    hash_level(l3, 4, IV, PARENT_FLAGS, l4);

    // Level 5: 4 → 2
    hash_level(l4, 2, IV, PARENT_FLAGS, l5);

    // Root: 2 → 1
    bytes32_t result;
    hash_level(l5, 1, IV, PARENT_FLAGS, result.bytes);
    return result;
}

MONAD_NAMESPACE_END
