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
#include <blake3.h>
#include <blake3_impl.h>
}

#include <category/core/bytes.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <boost/outcome/try.hpp>

#include <bit>
#include <cstdint>
#include <cstring>

MONAD_NAMESPACE_BEGIN

// MIP-8 Induced-Subtree Merkle Commitment (ISMC) over a 4096-byte storage
// page (64 pair-leaves of 64 bytes each).
//
//   Phase 1 — Leaf init:  hash the 64-byte pair-leaves where pair_bitmap is
//                         set with LEAF_IV (DERIVE_KEY_MATERIAL flag).
//   Phase 2 — Merge:      bottom-up bitmap-driven reduction. At each level
//                         d in [0, 6), merge sibling pairs (left index has
//                         bit d == 0, both share their parent at level d+1)
//                         using BLAKE3 (CHUNK_START | CHUNK_END). Singletons
//                         carry up implicitly because their bit stays in the
//                         live bitmap.
//   Phase 3 — Seal:       BLAKE3(slot_bitmap_le_16B || merge_root_32B). An
//                         empty page seals as BLAKE3(zero_bitmap_16B) only.
//
// scratch[i] is pair-indexed, not densely packed: a level's surviving entries
// are exactly the bits remaining in `bm`.

namespace
{
    constexpr size_t NUM_PAIRS = storage_page_t::SLOTS / 2; // 64
    constexpr char DOMAIN_KEY[] = "ultra_merkle_pair_leaf_domain___";
    static_assert(sizeof(DOMAIN_KEY) - 1 == 32);
    static_assert(NUM_PAIRS == 64);
    static_assert(std::has_single_bit(NUM_PAIRS), "must be power of 2");

    using slot_bitmap_t = unsigned __int128;

    uint32_t const *get_leaf_iv()
    {
        // LEAF_IV = compress(IV, PAIR_LEAF_KEY || zero_pad_to_64,
        //                    counter=0, flags=DERIVE_KEY_MATERIAL).
        static uint32_t const *const cached = [] {
            static uint32_t iv[8];
            uint8_t block[BLAKE3_BLOCK_LEN] = {};
            std::memcpy(block, DOMAIN_KEY, sizeof(DOMAIN_KEY) - 1);
            std::memcpy(iv, IV, sizeof(iv));
            blake3_compress_in_place(
                iv, block, BLAKE3_BLOCK_LEN, 0, DERIVE_KEY_MATERIAL);
            return iv;
        }();
        return cached;
    }

    struct page_bitmaps_t
    {
        slot_bitmap_t slot; // bit i = slot[i] is non-zero
        uint64_t pair; // bit i = slot[2i] or slot[2i+1] is non-zero
    };

    // Single-pass scan producing both bitmaps. Each 32-byte slot is
    // OR-reduced to a single u64 non-zero indicator; the pair bit is the
    // OR of its two slot indicators. Replaces the previous chain of
    // compute_slot_bitmap (full-page scan) + derive_pair_bitmap (full-bitmap
    // walk) with one walk over 64 pairs.
    page_bitmaps_t compute_page_bitmaps(storage_page_t const &page)
    {
        auto const slot_or = [](uint8_t const *const p) {
            uint64_t limbs[4];
            std::memcpy(limbs, p, sizeof(limbs));
            return limbs[0] | limbs[1] | limbs[2] | limbs[3];
        };

        page_bitmaps_t out{0, 0};
        slot_bitmap_t slot_mask = 1;
        uint64_t pair_mask = 1;
        for (size_t i = 0; i < NUM_PAIRS; ++i, pair_mask <<= 1) {
            uint64_t const lo = slot_or(page.slots[i * 2].bytes);
            uint64_t const hi = slot_or(page.slots[i * 2 + 1].bytes);
            if (lo != 0) {
                out.slot |= slot_mask;
            }
            slot_mask <<= 1;
            if (hi != 0) {
                out.slot |= slot_mask;
            }
            slot_mask <<= 1;
            if ((lo | hi) != 0) {
                out.pair |= pair_mask;
            }
        }
        return out;
    }

    void store_bitmap_le(slot_bitmap_t const bm, uint8_t out[16])
    {
        for (size_t i = 0; i < 16; ++i) {
            out[i] = static_cast<uint8_t>(bm >> (i * 8));
        }
    }

    bytes32_t
    blake3_seal(slot_bitmap_t const slot_bitmap, uint8_t const *root_32)
    {
        // BLAKE3(slot_bitmap_le_16B || merge_root_32B), or just the bitmap
        // when there is no root (empty page).
        //
        // The seal input is 16 or 48 bytes — a single sub-64-byte block, so
        // the BLAKE3 hash is exactly one compression with flags
        // CHUNK_START | CHUNK_END | ROOT (chunk is both first and last block,
        // and this is the root output). The high-level hasher_init/update/
        // finalize API would do the same thing under the hood plus a chunk
        // state machine and output-expansion bookkeeping we don't need; this
        // mirrors the get_leaf_iv() pattern above.
        uint8_t block[BLAKE3_BLOCK_LEN] = {}; // zero-padded to 64 bytes
        store_bitmap_le(slot_bitmap, block);
        uint8_t block_len = 16;
        if (root_32 != nullptr) {
            std::memcpy(block + 16, root_32, BLAKE3_OUT_LEN);
            block_len = 48;
        }
        uint32_t cv[8];
        std::memcpy(cv, IV, sizeof(cv));
        blake3_compress_in_place(
            cv, block, block_len, 0, CHUNK_START | CHUNK_END | ROOT);
        bytes32_t out;
        std::memcpy(out.bytes, cv, BLAKE3_OUT_LEN);
        return out;
    }
} // namespace

bytes32_t page_commit(storage_page_t const &page)
{
    auto const [slot_bitmap, pair_bitmap] = compute_page_bitmaps(page);
    if (pair_bitmap == 0) {
        // Empty page: seal the zero bitmap.
        return blake3_seal(0, nullptr);
    }

    // Phase 1 — Leaf init: hash active pair-leaves with LEAF_IV.
    // scratch is pair-indexed (entry i is meaningful iff bit i is in
    // pair_bitmap).
    bytes32_t scratch[NUM_PAIRS];
    {
        uint8_t const *inputs[NUM_PAIRS]{};
        uint8_t indices[NUM_PAIRS]{};
        size_t n = 0;
        uint64_t bits = pair_bitmap;
        while (bits != 0) {
            auto const idx = static_cast<uint8_t>(std::countr_zero(bits));
            indices[n] = idx;
            // slots are contiguous in memory: this points to the 64-byte
            // pair (slot[idx*2] || slot[idx*2 + 1]) that BLAKE3 will read.
            inputs[n] = page.slots[idx * 2].bytes;
            ++n;
            bits &= bits - 1; // clear the lowest set bit
        }
        bytes32_t flat_out[NUM_PAIRS];
        blake3_hash_many(
            inputs,
            n,
            1,
            get_leaf_iv(),
            0,
            false,
            DERIVE_KEY_MATERIAL,
            0,
            0,
            reinterpret_cast<uint8_t *>(flat_out));
        for (size_t i = 0; i < n; ++i) {
            scratch[indices[i]] = flat_out[i];
        }
    }

    // Phase 2 — Merge: bitmap-driven bottom-up reduction.
    //
    // Invariant: scratch[i] holds the live node whose representative
    // leaf-index is i, exactly when bit i of bm is set. Singletons that
    // don't pair this level need no copy, they stay in scratch with
    // their bit in bm and reappear at the next level. When two indices
    // (prev, pos) pair, we hash their values into scratch[prev] and clear
    // bit `pos` from bm; the merged node keeps the left's representative
    // index so the level-d+1 sibling check works unchanged.
    //
    // The popcount==1 case is handled by the loop condition without
    // entering the body.
    // Per-level scratchpads, sized to NUM_PAIRS/2 because at most half of
    // the surviving entries can pair into merges in any one level. Each
    // merge hashes scratch[left] || scratch[right] and writes the result
    // back to scratch[left]; scratch[right] is abandoned (its bit gets
    // cleared from bm). Hoisted above the level loop so inputs[i] = blocks[i]
    // is a one-time fixup, and the schedule + stitch passes inside each
    // level can run as separate predictable loops.
    uint8_t lefts[NUM_PAIRS / 2]; // index kept in bm; receives merged hash
    uint8_t rights[NUM_PAIRS / 2]; // index cleared from bm; slot abandoned
    uint8_t blocks[NUM_PAIRS / 2]
                  [BLAKE3_BLOCK_LEN]; // (left || right) bytes to hash
    uint8_t const *inputs[NUM_PAIRS / 2]; // pointers into blocks[]
    bytes32_t flat_out[NUM_PAIRS / 2];
    for (size_t j = 0; j < NUM_PAIRS / 2; ++j) {
        inputs[j] = blocks[j];
    }

    uint64_t bm = pair_bitmap;
    for (uint8_t bit = 0; bit < 6 && std::popcount(bm) > 1; ++bit) {
        // Pass 1 — schedule: walk surviving indices in ascending order and
        // record sibling pairs. Pure bitmap arithmetic, no memory traffic
        // into scratch[]. Branch predictor and prefetcher friendly.
        size_t merge_count = 0;
        uint64_t bits = bm;
        uint8_t prev = 0xFF;
        while (bits != 0) {
            auto const pos = static_cast<uint8_t>(std::countr_zero(bits));
            bits &= bits - 1;
            bool const sibling = prev != 0xFF &&
                                 (prev >> (bit + 1)) == (pos >> (bit + 1)) &&
                                 ((prev >> bit) & 1) == 0;
            if (sibling) {
                lefts[merge_count] = prev;
                rights[merge_count] = pos;
                ++merge_count;
                prev = 0xFF;
            }
            else {
                prev = pos;
            }
        }

        if (merge_count == 0) {
            continue;
        }

        // Pass 2 — stitch: pack scratch[left] || scratch[right] into a
        // 64-byte block per scheduled merge. Tight predictable loop.
        for (size_t j = 0; j < merge_count; ++j) {
            std::memcpy(
                blocks[j], scratch[lefts[j]].bytes, BLAKE3_OUT_LEN);
            std::memcpy(
                blocks[j] + BLAKE3_OUT_LEN,
                scratch[rights[j]].bytes,
                BLAKE3_OUT_LEN);
        }

        blake3_hash_many(
            inputs,
            merge_count,
            1,
            IV,
            0,
            false,
            0,
            CHUNK_START,
            CHUNK_END,
            reinterpret_cast<uint8_t *>(flat_out));
        for (size_t j = 0; j < merge_count; ++j) {
            scratch[lefts[j]] = flat_out[j];
            bm &= ~(static_cast<uint64_t>(1) << rights[j]);
        }
    }

    auto const root_idx = std::countr_zero(bm);

    // Phase 3 — Seal.
    return blake3_seal(slot_bitmap, scratch[root_idx].bytes);
}

// Storage page run-length encoding (RLE).
//
// Encodes a storage_page_t (SLOTS x 32-byte slot values) optimizing for
// minimum encoding size for both empty and non-empty slots, and fast
// encoding speed. Zero slots are collapsed into compact run headers;
// non-zero slots are compact-encoded (leading zeros stripped).
//
//   Header byte  | Meaning
//   -------------|----------------------------------------------------------
//   0x00..0x7F   | Zero-run of 0..127 slots (0x00 terminates encoding
//                | since it advances by 0).
//   0x80..0xFF   | Data-run of `(header & 0x7F) + 1` non-zero slots,
//                | each encoded via encode_bytes32_compact (leading-zero
//                | stripped, RLP string framing).
//
// Decoding stops when all SLOTS are accounted for or input is exhausted.
//
// Examples (SLOTS=32):
//   All-zero page     → 0x00                             (1 byte)
//   Slot 0 = 1, rest  → 0x80 0x01 0x00                   (1 + 1 + 1 = 3 bytes)
//   Slots 0-2 zero, slot 3 = 0xAB → 0x03 0x80 0x81 0xAB 0x00

byte_string encode_storage_page(storage_page_t const &page)
{
    byte_string encoded;
    constexpr uint8_t SLOTS = static_cast<uint8_t>(storage_page_t::SLOTS);
    constexpr bytes32_t ZERO{};
    uint8_t i = 0;
    while (i < SLOTS) {
        if (page[i] == ZERO) {
            // Count zero run
            uint8_t zeros = 1;
            while (i + zeros < SLOTS && page[i + zeros] == ZERO) {
                ++zeros;
            }
            if (i + zeros == SLOTS) {
                // Rest of page is zeros — emit terminator
                encoded.push_back(0x00);
                break;
            }
            // Emit zero-run count (0x01–0x7F)
            encoded.push_back(zeros);
            i += zeros;
        }
        else {
            // Count data run (max 128)
            uint8_t run = 1;
            while (i + run < SLOTS && run < 128 && page[i + run] != ZERO) {
                ++run;
            }
            // Emit data-run header: 0x80 | (count - 1), then compact-encoded
            // values
            encoded.push_back(static_cast<uint8_t>(0x80 | (run - 1)));
            for (uint8_t j = 0; j < run; ++j) {
                encoded += rlp::encode_bytes32_compact(page[i + j]);
            }
            i += run;
        }
    }
    return encoded;
}

Result<storage_page_t> decode_storage_page(byte_string_view enc)
{
    storage_page_t page{};
    size_t i = 0;
    while (i < storage_page_t::SLOTS) {
        if (MONAD_UNLIKELY(enc.empty())) {
            return rlp::DecodeError::InputTooShort;
        }
        uint8_t const header = enc[0];
        enc.remove_prefix(1);
        if (header == 0x00) {
            // Rest is zeros (already zero-initialized)
            break;
        }
        else if (header < 0x80) {
            // Zero-run of `header` words
            i += header;
        }
        else {
            // Data-run: compact-encoded slot values
            size_t const count = (header & 0x7F) + 1;
            if (MONAD_UNLIKELY(i + count > storage_page_t::SLOTS)) {
                return rlp::DecodeError::InputTooLong;
            }
            for (size_t j = 0; j < count; ++j) {
                BOOST_OUTCOME_TRY(
                    auto const slot_view, rlp::decode_string(enc));
                page[static_cast<uint8_t>(i + j)] = to_bytes(slot_view);
            }
            i += count;
        }
    }
    if (MONAD_UNLIKELY(i > storage_page_t::SLOTS)) {
        return rlp::DecodeError::InputTooLong;
    }
    return page;
}

MONAD_NAMESPACE_END
