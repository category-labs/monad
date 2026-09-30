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

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_NAMESPACE_BEGIN

// Deterministic storage page cache parameters. Sizes and capacities are in
// slot units, where a page's size is max(nonzero slots, 1). The growth gas
// these rely on is Traits::page_growth_cost(), and the block gas limit is
// header.gas_limit.
inline constexpr uint64_t PAGE_CACHE_CAPACITY = 10'000'000;
// A page admitted at the end of block b stays cached through about
// b + MIN_LIVENESS, whatever later blocks admit.
inline constexpr uint64_t PAGE_CACHE_MIN_LIVENESS = 100;
// Assumes a 150M block gas limit, so end_of_block asserts a block's records
// never exceed it; the ring size depends on this bound.
inline constexpr uint64_t PAGE_CACHE_MAX_ADMISSION_PER_BLOCK =
    PAGE_CACHE_CAPACITY / PAGE_CACHE_MIN_LIVENESS;
// 150M block gas / MAX_ADMISSION_PER_BLOCK.
inline constexpr uint64_t PAGE_CACHE_ADMISSION_GAS_PER_SLOT = 1'500;

// Log pages are storage pages of the system account. A record is an address
// then a page key.
inline constexpr size_t PAGE_CACHE_RECORD_SIZE = 52;
inline constexpr size_t PAGE_CACHE_LOG_HEADER_SIZE = 24;
inline constexpr uint64_t PAGE_CACHE_RECORDS_PER_LOG_PAGE =
    (storage_page_t::SLOTS * storage_page_t::SLOT_SIZE -
     PAGE_CACHE_LOG_HEADER_SIZE) /
    PAGE_CACHE_RECORD_SIZE;
inline constexpr uint64_t PAGE_CACHE_MAX_LOG_PAGES_PER_BLOCK =
    (PAGE_CACHE_MAX_ADMISSION_PER_BLOCK + PAGE_CACHE_RECORDS_PER_LOG_PAGE - 1) /
    PAGE_CACHE_RECORDS_PER_LOG_PAGE;

// Log pages in the ring. A stamp is a log page's sequence number before the
// modulo, shared by all of that page's records, and the log page with stamp
// s is at ring index s % RING_BUFFER_SIZE. At the end of a block, pages are
// evicted oldest stamp first while head + RING_BUFFER_SIZE < tail, so no
// ring index holding a cached page's record is ever rewritten. The tail
// advances at most MAX_LOG_PAGES_PER_BLOCK per block, so the ring alone keeps
// a record for at least MIN_LIVENESS full blocks. The system account
// converges to this many log pages, about 525 MB, and reconstruction reads
// at most that.
inline constexpr uint64_t PAGE_CACHE_RING_BUFFER_SIZE =
    PAGE_CACHE_MIN_LIVENESS * PAGE_CACHE_MAX_LOG_PAGES_PER_BLOCK;

// System account holding the log and cursor. Placeholder, outside the
// precompile set and the staking address.
inline constexpr Address PAGE_CACHE_ADDRESS =
    0x0000000000000000000000000000000000c4c4e0_address;

// Decision: every transaction deducts the requirement of each page it can
// afford, even one an earlier transaction in the block already qualified.
// When false, the first qualifying transaction covers the page.
inline constexpr bool PAGE_CACHE_EVERY_TX_DEDUCTS = true;

static_assert(PAGE_CACHE_MAX_ADMISSION_PER_BLOCK == 100'000);
static_assert(PAGE_CACHE_RECORDS_PER_LOG_PAGE == 78);
static_assert(PAGE_CACHE_MAX_LOG_PAGES_PER_BLOCK == 1'283);
static_assert(PAGE_CACHE_RING_BUFFER_SIZE == 128'300);
static_assert(PAGE_CACHE_RECORD_SIZE == sizeof(Address) + sizeof(bytes32_t));

// Page keys (slot key >> 7) of the system account's pages: 0 for the cursor
// and j + 1 for the log page at ring index j.
inline constexpr bytes32_t PAGE_CACHE_CURSOR_PAGE_KEY{};
bytes32_t page_cache_log_page_key(uint64_t ring_index);

// Cursor page, in slot 0: head in bytes 0..7, tail in bytes 8..15, big-endian,
// every other byte and slot zero. Both are in log page units: tail is the
// stamp of the next log page to write, head the smallest stamp of any cached
// page, or tail if none is cached.
struct PageCacheCursor
{
    uint64_t head{0};
    uint64_t tail{0};

    friend bool
    operator==(PageCacheCursor const &, PageCacheCursor const &) = default;
};

// Log page: the records of one block that share one stamp. Read as the
// page's 4,096 bytes, slot k holding bytes 32k .. 32k + 31: block number at
// byte 0, the stamp at byte 8, record count n at byte 16 (2 bytes), zeros to
// byte 24, then n records of address and page key, then zeros. A record is
// the page's StorageKey with a zero incarnation.
struct PageCacheLogPage
{
    uint64_t block_number{0};
    uint64_t stamp{0};
    std::vector<StorageKey> records;

    friend bool
    operator==(PageCacheLogPage const &, PageCacheLogPage const &) = default;
};

enum class PageCacheError
{
    Success = 0,
    CursorOutOfOrder,
    WrongStamp,
    BadRecordCount,
};

storage_page_t encode_cursor(PageCacheCursor const &);
Result<PageCacheCursor> decode_cursor(storage_page_t const &);

storage_page_t encode_log_page(
    uint64_t block_number, uint64_t stamp, std::span<StorageKey const>);
// Reads exactly n records. Rejects a page whose stamp is not
// `expected_stamp`, or whose n is 0 or above 78; a ring index never written
// is an empty page, stamp 0 with n == 0.
Result<PageCacheLogPage>
decode_log_page(storage_page_t const &, uint64_t expected_stamp);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::PageCacheError>
    : quick_status_code_from_enum_defaults<monad::PageCacheError>
{
    static constexpr auto const domain_name = "Page Cache Error";
    static constexpr auto const domain_uuid =
        "6b4fbc47-8259-499e-a66f-cd058242c9be";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
