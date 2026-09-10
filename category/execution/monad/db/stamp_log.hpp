// Copyright (C) 2026 Category Labs, Inc.
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

// The stamp log: block b writes its selected stamps as storage of
// STAMP_LOG_ADDRESS. The record is split into 32-byte words; word w of page i
// lives at slot key ((b mod CACHE_WINDOW_BLOCKS) * STAMP_LOG_PAGES_PER_SLOT +
// i) * 128 + w, so each 4 KB chunk is one MIP-8 page and ring slot
// b mod CACHE_WINDOW_BLOCKS is overwritten every window. Bytes beyond the
// record length are ignored by readers.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

inline constexpr uint64_t STAMP_LOG_PAGES_PER_SLOT = 128;
inline constexpr size_t STAMP_LOG_HEADER_BYTES = 16;
inline constexpr size_t STAMP_LOG_PAGE_BYTES =
    storage_page_t::SLOTS * storage_page_t::SLOT_SIZE;

struct StampLogRecord
{
    uint64_t block;
    std::vector<Address> accounts;
    std::vector<StorageKey> storage;
};

// block_number (u64 LE) || n_accounts (u32 LE) || n_pages (u32 LE) ||
// account keys (20 bytes each) || page keys (60 bytes each), in selection
// order.
byte_string encode_stamp_log_record(
    uint64_t block, std::vector<Address> const &accounts,
    std::vector<StorageKey> const &storage);

// Header of a record: (block, n_accounts, n_pages); nullopt when shorter
// than a header.
struct StampLogHeader
{
    uint64_t block;
    uint32_t n_accounts;
    uint32_t n_pages;

    size_t record_bytes() const
    {
        return STAMP_LOG_HEADER_BYTES + 20 * size_t{n_accounts} +
               StorageKey::k_bytes * size_t{n_pages};
    }
};

std::optional<StampLogHeader> decode_stamp_log_header(byte_string_view);

// Full record; nullopt when the bytes are shorter than the header claims.
std::optional<StampLogRecord> decode_stamp_log_record(byte_string_view);

// Page key (slot key >> 7) of page `page_index` of block `block`'s ring slot.
bytes32_t stamp_log_page_key(uint64_t block, uint64_t page_index);

// Number of pages a record of `record_bytes` occupies.
inline size_t stamp_log_pages(size_t const record_bytes)
{
    return (record_bytes + STAMP_LOG_PAGE_BYTES - 1) / STAMP_LOG_PAGE_BYTES;
}

// Page `page_index` of the record: words are slots, zero words are absent.
storage_page_t stamp_log_page(byte_string_view record, size_t page_index);

// Append the words of a page back into a record buffer (page_index-th chunk).
void stamp_log_append_page(byte_string &record, storage_page_t const &page);

MONAD_NAMESPACE_END
