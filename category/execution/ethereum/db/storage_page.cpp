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

#include <category/core/bytes.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/storage_page.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

MONAD_NAMESPACE_BEGIN

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
//   All-zero page     → 0x00                              (1 byte)
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

Result<storage_page_t> decode_storage_page(byte_string_view &enc)
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
