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

#include <category/core/assert.h>
#include <category/core/int.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/page_cache.hpp>
#include <category/execution/monad/db/storage_page.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <array>
#include <cstring>
#include <initializer_list>
#include <span>

MONAD_NAMESPACE_BEGIN

namespace
{
    constexpr size_t PAGE_BYTES =
        storage_page_t::SLOTS * storage_page_t::SLOT_SIZE;
    constexpr size_t COUNT_OFFSET = 16;
    constexpr size_t KEY_OFFSET = sizeof(Address) + sizeof(Incarnation);

    using PageBytes = std::array<uint8_t, PAGE_BYTES>;

    constexpr size_t record_offset(size_t const k)
    {
        return PAGE_CACHE_LOG_HEADER_SIZE + PAGE_CACHE_RECORD_SIZE * k;
    }

    storage_page_t to_page(PageBytes const &bytes)
    {
        storage_page_t page;
        for (uint8_t off = 0; off < storage_page_t::SLOTS; ++off) {
            bytes32_t word;
            std::memcpy(
                word.bytes,
                bytes.data() + off * storage_page_t::SLOT_SIZE,
                sizeof(word.bytes));
            page.set(off, word);
        }
        return page;
    }

    PageBytes to_bytes(storage_page_t const &page)
    {
        PageBytes bytes{};
        for (uint8_t off = 0; off < storage_page_t::SLOTS; ++off) {
            bytes32_t const word = page[off];
            std::memcpy(
                bytes.data() + off * storage_page_t::SLOT_SIZE,
                word.bytes,
                sizeof(word.bytes));
        }
        return bytes;
    }
}

bytes32_t page_cache_log_page_key(uint64_t const ring_index)
{
    MONAD_ASSERT(ring_index < PAGE_CACHE_RING_BUFFER_SIZE);
    return bytes32_t{ring_index + 1};
}

storage_page_t encode_cursor(PageCacheCursor const &cursor)
{
    MONAD_ASSERT(cursor.head <= cursor.tail);
    bytes32_t word{};
    store_be(word.bytes, cursor.head);
    store_be(word.bytes + 8, cursor.tail);
    storage_page_t page;
    page.set(0, word);
    return page;
}

Result<PageCacheCursor> decode_cursor(storage_page_t const &page)
{
    bytes32_t const word = page[0];
    PageCacheCursor const cursor{
        .head = load_be_unsafe<uint64_t>(word.bytes),
        .tail = load_be_unsafe<uint64_t>(word.bytes + 8)};
    if (cursor.head > cursor.tail) {
        return PageCacheError::CursorOutOfOrder;
    }
    return cursor;
}

storage_page_t encode_log_page(
    uint64_t const block_number, uint64_t const stamp,
    std::span<StorageKey const> const records)
{
    MONAD_ASSERT(
        !records.empty() && records.size() <= PAGE_CACHE_RECORDS_PER_LOG_PAGE);
    PageBytes bytes{};
    store_be(bytes.data(), block_number);
    store_be(bytes.data() + 8, stamp);
    bytes[COUNT_OFFSET] = static_cast<uint8_t>(records.size() >> 8);
    bytes[COUNT_OFFSET + 1] = static_cast<uint8_t>(records.size());
    for (size_t k = 0; k < records.size(); ++k) {
        uint8_t const *const key = records[k].bytes;
        MONAD_ASSERT(
            load_le_unsafe<uint64_t>(key + sizeof(Address)) == 0,
            "page cache record with a nonzero incarnation");
        uint8_t *const rec = bytes.data() + record_offset(k);
        std::memcpy(rec, key, sizeof(Address));
        std::memcpy(rec + sizeof(Address), key + KEY_OFFSET, sizeof(bytes32_t));
    }
    return to_page(bytes);
}

Result<PageCacheLogPage>
decode_log_page(storage_page_t const &page, uint64_t const expected_stamp)
{
    PageBytes const bytes = to_bytes(page);
    PageCacheLogPage log_page{
        .block_number = load_be_unsafe<uint64_t>(bytes.data()),
        .stamp = load_be_unsafe<uint64_t>(bytes.data() + 8),
        .records = {}};
    if (log_page.stamp != expected_stamp) {
        return PageCacheError::WrongStamp;
    }
    size_t const n =
        (size_t{bytes[COUNT_OFFSET]} << 8) | bytes[COUNT_OFFSET + 1];
    if (n == 0 || n > PAGE_CACHE_RECORDS_PER_LOG_PAGE) {
        return PageCacheError::BadRecordCount;
    }
    log_page.records.reserve(n);
    for (size_t k = 0; k < n; ++k) {
        uint8_t const *const rec = bytes.data() + record_offset(k);
        Address address;
        bytes32_t key;
        std::memcpy(address.bytes, rec, sizeof(Address));
        std::memcpy(key.bytes, rec + sizeof(Address), sizeof(bytes32_t));
        log_page.records.emplace_back(address, Incarnation{0, 0}, key);
    }
    return log_page;
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::PageCacheError>::mapping> const &
quick_status_code_from_enum<monad::PageCacheError>::value_mappings()
{
    using monad::PageCacheError;

    static std::initializer_list<mapping> const v = {
        {PageCacheError::Success, "success", {errc::success}},
        {PageCacheError::CursorOutOfOrder, "cursor head after tail", {}},
        {PageCacheError::WrongStamp, "log page has the wrong stamp", {}},
        {PageCacheError::BadRecordCount, "log page record count invalid", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
