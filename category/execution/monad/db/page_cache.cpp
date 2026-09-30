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

#include <initializer_list>

MONAD_NAMESPACE_BEGIN

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
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
