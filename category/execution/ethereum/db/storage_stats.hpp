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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <algorithm>
#include <atomic>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

// Per-block storage access counters, reported and reset by
// TrieDb::print_stats. A read is a slot read reaching BlockState (one per
// slot per transaction at most), a write a slot changed at commit. "First
// page" is slot number < FIRST_PAGE_SLOTS, the slots a partitioned layout
// keeps with the account; counted on every layout so a slot-layout run shows
// what a partitioned one would serve from the account leaf.
namespace storage_stats
{
    inline constexpr unsigned FIRST_PAGE_SLOTS = 128;

    inline std::atomic<uint64_t> reads{0};
    inline std::atomic<uint64_t> reads_first_page{0};
    inline std::atomic<uint64_t> writes{0};
    inline std::atomic<uint64_t> writes_first_page{0};

    inline bool is_first_page(bytes32_t const &slot)
    {
        return std::all_of(
                   slot.bytes,
                   slot.bytes + 31,
                   [](unsigned char const b) { return b == 0; }) &&
               slot.bytes[31] < FIRST_PAGE_SLOTS;
    }

    inline void on_read(bytes32_t const &slot)
    {
        reads.fetch_add(1, std::memory_order_relaxed);
        if (is_first_page(slot)) {
            reads_first_page.fetch_add(1, std::memory_order_relaxed);
        }
    }

    inline void on_write(bytes32_t const &slot)
    {
        writes.fetch_add(1, std::memory_order_relaxed);
        if (is_first_page(slot)) {
            writes_first_page.fetch_add(1, std::memory_order_relaxed);
        }
    }
}

MONAD_NAMESPACE_END
