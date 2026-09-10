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

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/stamp_log.hpp>

#include <cstring>

MONAD_NAMESPACE_BEGIN

namespace
{
    void put_u64(byte_string &out, uint64_t const v)
    {
        for (unsigned i = 0; i < 8; ++i) {
            out.push_back(static_cast<unsigned char>(v >> (8 * i)));
        }
    }

    void put_u32(byte_string &out, uint32_t const v)
    {
        for (unsigned i = 0; i < 4; ++i) {
            out.push_back(static_cast<unsigned char>(v >> (8 * i)));
        }
    }

    uint64_t get_u64(unsigned char const *const p)
    {
        uint64_t v = 0;
        for (unsigned i = 0; i < 8; ++i) {
            v |= static_cast<uint64_t>(p[i]) << (8 * i);
        }
        return v;
    }

    uint32_t get_u32(unsigned char const *const p)
    {
        uint32_t v = 0;
        for (unsigned i = 0; i < 4; ++i) {
            v |= static_cast<uint32_t>(p[i]) << (8 * i);
        }
        return v;
    }
}

byte_string encode_stamp_log_record(
    uint64_t const block, std::vector<Address> const &accounts,
    std::vector<StorageKey> const &storage)
{
    byte_string out;
    out.reserve(
        STAMP_LOG_HEADER_BYTES + 20 * accounts.size() +
        StorageKey::k_bytes * storage.size());
    put_u64(out, block);
    put_u32(out, static_cast<uint32_t>(accounts.size()));
    put_u32(out, static_cast<uint32_t>(storage.size()));
    for (auto const &a : accounts) {
        out.append(a.bytes, sizeof(a.bytes));
    }
    for (auto const &k : storage) {
        out.append(k.bytes, sizeof(k.bytes));
    }
    return out;
}

std::optional<StampLogHeader> decode_stamp_log_header(byte_string_view const in)
{
    if (in.size() < STAMP_LOG_HEADER_BYTES) {
        return std::nullopt;
    }
    return StampLogHeader{
        .block = get_u64(in.data()),
        .n_accounts = get_u32(in.data() + 8),
        .n_pages = get_u32(in.data() + 12)};
}

std::optional<StampLogRecord> decode_stamp_log_record(byte_string_view const in)
{
    auto const header = decode_stamp_log_header(in);
    if (!header.has_value() || in.size() < header->record_bytes()) {
        return std::nullopt;
    }
    StampLogRecord rec;
    rec.block = header->block;
    unsigned char const *p = in.data() + STAMP_LOG_HEADER_BYTES;
    rec.accounts.reserve(header->n_accounts);
    for (uint32_t i = 0; i < header->n_accounts; ++i) {
        Address a;
        std::memcpy(a.bytes, p, sizeof(a.bytes));
        p += sizeof(a.bytes);
        rec.accounts.push_back(a);
    }
    rec.storage.reserve(header->n_pages);
    for (uint32_t i = 0; i < header->n_pages; ++i) {
        StorageKey k;
        std::memcpy(k.bytes, p, sizeof(k.bytes));
        p += sizeof(k.bytes);
        rec.storage.push_back(k);
    }
    return rec;
}

bytes32_t stamp_log_page_key(uint64_t const block, uint64_t const page_index)
{
    MONAD_ASSERT(page_index < STAMP_LOG_PAGES_PER_SLOT);
    uint256_t const index =
        (block % CACHE_WINDOW_BLOCKS) * STAMP_LOG_PAGES_PER_SLOT + page_index;
    return store_be_as<bytes32_t>(index);
}

storage_page_t
stamp_log_page(byte_string_view const record, size_t const page_index)
{
    storage_page_t page;
    size_t const begin = page_index * STAMP_LOG_PAGE_BYTES;
    for (size_t w = 0; w < storage_page_t::SLOTS; ++w) {
        size_t const off = begin + w * storage_page_t::SLOT_SIZE;
        if (off >= record.size()) {
            break;
        }
        bytes32_t word{};
        size_t const n =
            std::min(storage_page_t::SLOT_SIZE, record.size() - off);
        std::memcpy(word.bytes, record.data() + off, n);
        page.set(static_cast<uint8_t>(w), word);
    }
    return page;
}

void stamp_log_append_page(byte_string &record, storage_page_t const &page)
{
    for (size_t w = 0; w < storage_page_t::SLOTS; ++w) {
        bytes32_t const word = page[static_cast<uint8_t>(w)];
        record.append(word.bytes, sizeof(word.bytes));
    }
}

MONAD_NAMESPACE_END
