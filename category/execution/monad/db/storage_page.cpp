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

#if !defined(__BMI2__)
    #error                                                                     \
        "storage_page impl requires BMI2 (_pext_u64). Build with a supported toolchain."
#endif

#include <immintrin.h>

#include <bit>
#include <cstdint>
#include <cstring>

MONAD_NAMESPACE_BEGIN

uint64_t storage_page_t::pair_bitmap() const
{
    // OR each odd bit into the even bit below it, then compress the
    // even bits: pair i of the result comes from slots 2i and 2i+1.
    constexpr uint64_t even_bits = 0x5555555555555555ULL;
    auto const lo = static_cast<uint64_t>(bitmap_);
    auto const hi = static_cast<uint64_t>(bitmap_ >> 64);
    uint64_t const lo_pairs = _pext_u64(lo | (lo >> 1), even_bits);
    uint64_t const hi_pairs = _pext_u64(hi | (hi >> 1), even_bits);
    return lo_pairs | (hi_pairs << 32);
}

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
    constexpr size_t NUM_PAIRS = storage_page_t::NUM_PAIRS; // 64
    constexpr char DOMAIN_KEY[] = "ultra_merkle_pair_leaf_domain___";
    static_assert(sizeof(DOMAIN_KEY) - 1 == 32);
    static_assert(NUM_PAIRS == 64);
    static_assert(std::has_single_bit(NUM_PAIRS), "must be power of 2");

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

    bytes32_t blake3_seal(
        storage_page_t::bitmap_t const slot_bitmap, uint8_t const *root_32)
    {
        // blake3_compress(slot_bitmap_le_16B || merge_root_32B), or just the
        // bitmap when there is no root (empty page).
        uint8_t block[BLAKE3_BLOCK_LEN] = {}; // zero-padded to 64 bytes
        static_assert(std::endian::native == std::endian::little);
        std::memcpy(block, &slot_bitmap, sizeof(slot_bitmap)); // little endian
        uint8_t len = static_cast<uint8_t>(sizeof(storage_page_t::bitmap_t));
        if (root_32 != nullptr) {
            std::memcpy(block + sizeof(slot_bitmap), root_32, BLAKE3_OUT_LEN);
            len += BLAKE3_OUT_LEN; // 16 + 32 = 48
        }
        uint32_t cv[8];
        std::memcpy(cv, IV, sizeof(cv));
        blake3_compress_in_place(
            cv, block, len, 0, CHUNK_START | CHUNK_END | ROOT);
        bytes32_t out;
        std::memcpy(out.bytes, cv, BLAKE3_OUT_LEN);
        return out;
    }

    // Phase 1 — Leaf init: hash the 64-byte (left || right) pair-leaf for
    // every bit set in pair_bitmap with LEAF_IV (DERIVE_KEY_MATERIAL flag).
    // Writes results into `scratch`, indexed by pair index; entries whose
    // bit is not set in pair_bitmap are left untouched.
    void init_leaves(
        storage_page_t const &page, uint64_t const pair_bitmap,
        bytes32_t (&scratch)[NUM_PAIRS])
    {
        uint8_t valid_pairs[NUM_PAIRS][BLAKE3_BLOCK_LEN];
        uint8_t const *inputs[NUM_PAIRS] = {};
        uint8_t indices[NUM_PAIRS];
        size_t n = 0;
        for (uint64_t bits = pair_bitmap; bits != 0; bits &= bits - 1, ++n) {
            auto const i = static_cast<uint8_t>(std::countr_zero(bits));
            auto const left_idx = static_cast<uint8_t>(2 * i);
            auto const right_idx = static_cast<uint8_t>(left_idx + 1);
            std::memcpy(valid_pairs[n], page[left_idx].bytes, BLAKE3_OUT_LEN);
            std::memcpy(
                valid_pairs[n] + BLAKE3_OUT_LEN,
                page[right_idx].bytes,
                BLAKE3_OUT_LEN);
            indices[n] = i;
            inputs[n] = valid_pairs[n];
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

    // Phase 2 — Merge one level: bitmap-driven sibling reduction.
    //
    // Invariant on entry: scratch[i] holds the live node whose
    // representative leaf-index is i, exactly when bit i of bm is set.
    // Singletons that don't pair this level need no copy; they stay in
    // scratch with their bit in bm and reappear at the next level. When
    // two indices (prev, pos) pair, we hash their values into
    // scratch[prev] and clear bit `pos` from bm; the merged node keeps
    // the left's representative index so the level-d+1 sibling check
    // works unchanged. Returns the updated bm.
    uint64_t merge_at_level(
        uint8_t const level, uint64_t bm, bytes32_t (&scratch)[NUM_PAIRS])
    {
        // Per-level scratchpads, sized to NUM_PAIRS/2 because at most
        // half of the surviving entries can pair into merges this level.
        // Each merge hashes scratch[left] || scratch[right] and writes
        // the result back to scratch[left]; scratch[right] is abandoned
        // (its bit gets cleared from bm).
        uint8_t lefts[NUM_PAIRS / 2]; // index kept in bm; receives merged hash
        uint8_t rights[NUM_PAIRS / 2]; // index cleared from bm; slot abandoned
        uint8_t blocks[NUM_PAIRS / 2]
                      [BLAKE3_BLOCK_LEN]; // (left || right) bytes to hash
        uint8_t const *inputs[NUM_PAIRS / 2] = {}; // pointers into blocks[]
        size_t merge_count = 0;

        // Walk surviving indices in ascending order, pairing siblings and
        // packing each merge block (left || right) in the same pass.
        uint64_t bits = bm;
        uint8_t prev = 0xFF;
        while (bits != 0) {
            auto const pos = static_cast<uint8_t>(std::countr_zero(bits));
            bits &= bits - 1;
            bool const sibling =
                prev != 0xFF && (prev >> (level + 1)) == (pos >> (level + 1)) &&
                ((prev >> level) & 1) == 0;
            if (sibling) {
                lefts[merge_count] = prev;
                rights[merge_count] = pos;
                std::memcpy(
                    blocks[merge_count], scratch[prev].bytes, BLAKE3_OUT_LEN);
                std::memcpy(
                    blocks[merge_count] + BLAKE3_OUT_LEN,
                    scratch[pos].bytes,
                    BLAKE3_OUT_LEN);
                inputs[merge_count] = blocks[merge_count];
                ++merge_count;
                prev = 0xFF;
            }
            else {
                prev = pos;
            }
        }

        if (merge_count == 0) {
            return bm;
        }

        bytes32_t flat_out[NUM_PAIRS / 2];
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
        return bm;
    }

    // Wraps Phase 1 + Phase 2: runs leaf init then the level-by-level
    // merge loop, returning the single surviving subtree CV. Caller
    // must ensure the page is non-empty (pair_bitmap != 0).
    bytes32_t compute_nonempty_subtree_root(
        storage_page_t const &page, uint64_t const pair_bitmap)
    {
        bytes32_t scratch[NUM_PAIRS];
        init_leaves(page, pair_bitmap, scratch);

        uint64_t bm = pair_bitmap;
        for (uint8_t level = 0; level < 6 && std::popcount(bm) > 1; ++level) {
            bm = merge_at_level(level, bm, scratch);
        }

        auto const root_idx = std::countr_zero(bm);
        return scratch[root_idx];
    }
} // namespace

bytes32_t page_commit(storage_page_t const &page)
{
    if (page.is_empty()) {
        return blake3_seal(0, nullptr);
    }
    auto const slot_bitmap = page.bitmap();
    uint64_t const pair_bitmap = page.pair_bitmap();
    bytes32_t const root = compute_nonempty_subtree_root(page, pair_bitmap);
    return blake3_seal(slot_bitmap, root.bytes);
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
// Decoding is strict: only the canonical encoding produced by
// encode_storage_page is accepted (see decode_storage_page below).
//
// Examples:
//   All-zero page     → 0x00                             (1 byte)
//   Slot 0 = 1, rest  → 0x80 0x01 0x00                   (1 + 1 + 1 = 3 bytes)
//   Slots 0-2 zero, slot 3 = 0xAB → 0x03 0x80 0x81 0xAB 0x00

byte_string encode_storage_page(storage_page_t const &page)
{
    byte_string encoded;
    // Worst case: 33 bytes per compact-framed value plus one header byte
    // per run (at most SLOTS headers) and the terminator. This deliberately
    // overallocates (up to ~4KB transient for a full page of small values);
    // the buffer is short-lived since the caller copies it into the final
    // DB encoding, so the unused capacity never outlives this call.
    constexpr uint8_t SLOTS = static_cast<uint8_t>(storage_page_t::SLOTS);
    encoded.reserve(page.size() * 33 + SLOTS + 1);
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
            // Count data run (max SLOTS)
            uint8_t run = 1;
            while (i + run < SLOTS && run < SLOTS && page[i + run] != ZERO) {
                ++run;
            }
            // Emit data-run header: SLOTS | (count - 1), then compact-encoded
            // values
            encoded.push_back(static_cast<uint8_t>(SLOTS | (run - 1)));
            for (uint8_t j = 0; j < run; ++j) {
                encoded += rlp::encode_bytes32_compact(page[i + j]);
            }
            i += run;
        }
    }
    return encoded;
}

// Strict decoder: accepts exactly the encodings encode_storage_page
// produces, so encode(decode(x)) == x for every accepted input. This keeps
// the encoding usable as a canonical identity (hashing, byte comparison).
// Rejected non-canonical forms:
//   - adjacent runs of the same type (split zero-runs or data-runs)
//   - a zero-run reaching the end of the page (must be the 0x00 terminator)
//   - a zero-run directly before the terminator (must fold into it)
//   - zero values inside a data run
//   - slot values with leading zero bytes (non-minimal compact form)
Result<storage_page_t> decode_storage_page(byte_string_view enc)
{
    storage_page_t page{};
    size_t i = 0;
    bool at_start = true;
    bool prev_is_data_run = false;
    while (i < storage_page_t::SLOTS) {
        if (MONAD_UNLIKELY(enc.empty())) {
            return rlp::DecodeError::InputTooShort;
        }
        uint8_t const header = enc[0];
        enc.remove_prefix(1);
        if (header == 0x00) {
            // Terminator: rest of page is zeros (already zero-initialized).
            // Canonical only for an empty page or directly after a data run.
            if (MONAD_UNLIKELY(!at_start && !prev_is_data_run)) {
                return rlp::DecodeError::NonCanonical;
            }
            break;
        }
        if (header < storage_page_t::SLOTS) {
            // Zero-run of `header` words. Canonically appears only between
            // data runs (or before the first one).
            if (MONAD_UNLIKELY(!at_start && !prev_is_data_run)) {
                return rlp::DecodeError::NonCanonical;
            }
            i += header;
            if (MONAD_UNLIKELY(i >= storage_page_t::SLOTS)) {
                return rlp::DecodeError::NonCanonical;
            }
            prev_is_data_run = false;
        }
        else {
            // Data-run: compact-encoded slot values
            if (MONAD_UNLIKELY(prev_is_data_run)) {
                return rlp::DecodeError::NonCanonical;
            }
            size_t const count = (header & 0x7F) + 1;
            if (MONAD_UNLIKELY(i + count > storage_page_t::SLOTS)) {
                return rlp::DecodeError::InputTooLong;
            }
            for (size_t j = 0; j < count; ++j) {
                BOOST_OUTCOME_TRY(
                    auto const value, rlp::decode_bytes32_compact(enc));
                // A zero value belongs to a zero-run, never a data run.
                if (MONAD_UNLIKELY(value == bytes32_t{})) {
                    return rlp::DecodeError::NonCanonical;
                }
                page.set(static_cast<uint8_t>(i + j), value);
            }
            i += count;
            prev_is_data_run = true;
        }
        at_start = false;
    }
    if (MONAD_UNLIKELY(!enc.empty())) {
        return rlp::DecodeError::InputTooLong;
    }
    return page;
}

MONAD_NAMESPACE_END
