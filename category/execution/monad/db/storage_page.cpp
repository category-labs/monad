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

// ── COO / Bitmap page encoding
// ────────────────────────────────────────────────────
//
// Two cases based on population count k (number of non-zero slots):
//
//   k < 16  →  COO:     [0|k](1B) [indices](kB) [values](k×32B)
//   k >= 16 →  Bitmap:  [1|0](1B) [128-bit mask](16B) [values](k×32B)
//
// Crossover at k=16: COO = 1+33k = 529, Bitmap = 17+32k = 529.

static constexpr uint8_t COO_TAG = 0x00;
static constexpr uint8_t BITMAP_TAG = 0x80;
static constexpr size_t BITMAP_BYTES = storage_page_t::SLOTS / 8; // 16
static constexpr size_t COO_THRESHOLD = 16;

byte_string page_encode(storage_page_t const &page)
{
    static constexpr bytes32_t ZERO{};
    static constexpr size_t SZ = storage_page_t::SLOT_SIZE;

    // Collect non-zero slot indices.
    uint8_t indices[storage_page_t::SLOTS];
    size_t k = 0;
    for (size_t i = 0; i < storage_page_t::SLOTS; ++i) {
        if (page.slots[i] != ZERO) {
            indices[k++] = static_cast<uint8_t>(i);
        }
    }

    if (k < COO_THRESHOLD) {
        byte_string out(1 + k + k * SZ, 0);
        out[0] = COO_TAG | static_cast<uint8_t>(k);
        std::memcpy(out.data() + 1, indices, k);
        for (size_t i = 0; i < k; ++i) {
            std::memcpy(
                out.data() + 1 + k + i * SZ, page.slots[indices[i]].bytes, SZ);
        }
        return out;
    }

    // Bitmap path.
    uint8_t mask[BITMAP_BYTES] = {};
    for (size_t i = 0; i < k; ++i) {
        uint8_t const idx = indices[i];
        mask[idx / 8] |= uint8_t(1) << (idx % 8);
    }

    byte_string out(1 + BITMAP_BYTES + k * SZ, 0);
    out[0] = BITMAP_TAG;
    std::memcpy(out.data() + 1, mask, BITMAP_BYTES);
    for (size_t i = 0; i < k; ++i) {
        std::memcpy(
            out.data() + 1 + BITMAP_BYTES + i * SZ,
            page.slots[indices[i]].bytes,
            SZ);
    }
    return out;
}

storage_page_t page_decode(uint8_t const *data, size_t const len)
{
    static constexpr size_t SZ = storage_page_t::SLOT_SIZE;
    storage_page_t page{};

    if (len == 0) {
        return page;
    }

    uint8_t const header = data[0];

    if ((header & BITMAP_TAG) == 0) {
        // COO
        size_t const k = header & 0x7F;
        MONAD_ASSERT(len == 1 + k + k * SZ);
        uint8_t const *idx_ptr = data + 1;
        uint8_t const *val_ptr = data + 1 + k;
        for (size_t i = 0; i < k; ++i) {
            MONAD_ASSERT(idx_ptr[i] < storage_page_t::SLOTS);
            std::memcpy(page.slots[idx_ptr[i]].bytes, val_ptr + i * SZ, SZ);
        }
    }
    else {
        // Bitmap
        MONAD_ASSERT(len >= 1 + BITMAP_BYTES);
        uint8_t const *mask = data + 1;
        uint8_t const *val_ptr = data + 1 + BITMAP_BYTES;
        size_t vi = 0;
        for (size_t i = 0; i < storage_page_t::SLOTS; ++i) {
            if (mask[i / 8] & (uint8_t(1) << (i % 8))) {
                MONAD_ASSERT(1 + BITMAP_BYTES + (vi + 1) * SZ <= len);
                std::memcpy(page.slots[i].bytes, val_ptr + vi * SZ, SZ);
                ++vi;
            }
        }
    }

    return page;
}

byte_string page_encode_slot(bytes32_t const &val)
{
    static constexpr bytes32_t ZERO{};
    static constexpr size_t SZ = storage_page_t::SLOT_SIZE;

    if (val == ZERO) {
        return byte_string(1, COO_TAG);
    }

    byte_string out(1 + 1 + SZ, 0);
    out[0] = COO_TAG | 1;
    out[1] = 0;
    std::memcpy(out.data() + 2, val.bytes, SZ);
    return out;
}

MONAD_NAMESPACE_END
