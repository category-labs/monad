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

#include <category/mpt/config.hpp>

#include <cstdint>
#include <type_traits>

MONAD_MPT_NAMESPACE_BEGIN

namespace detail
{
    // Lifetime totals, never reset. Every field must be monotonically
    // increasing: delta_since() subtracts fieldwise to recover what a single
    // upsert contributed.
    struct TrieUpdateCollectedStats
    {
        // counters
        uint64_t nodes_created_or_updated{0};
        // reads stats
        uint64_t nreads_compaction{0};
        // [0]: fast, [1]: slow
        uint64_t nreads_before_compact_offset[2] = {0, 0};
        uint64_t nreads_after_compact_offset[2] = {0, 0};
        uint64_t bytes_read_before_compact_offset[2] = {0, 0};
        uint64_t bytes_read_after_compact_offset[2] = {0, 0};

        // node copy stats
        uint64_t compacted_nodes_in_fast{0}; // fast to slow
        uint64_t compacted_nodes_in_slow{0}; // slow to slow
        uint64_t nodes_copied_fast_to_fast_for_fast{0};
        uint64_t nodes_copied_fast_to_fast_for_slow{0};
        uint64_t nodes_copied_slow_to_fast_for_slow{0};

        // bytes copied stats
        // Sum of the following three equals the current block slow ring
        // growth
        uint64_t compacted_bytes_in_fast{0}; // copied from fast to slow
        // Doubles as the GC-efficiency input to advance_compact_offsets, which
        // makes it load-bearing state and not just observability.
        uint64_t compacted_bytes_in_slow{0}; // copied from slow to slow
        uint64_t bytes_copied_slow_to_fast_for_slow{0};

        // expire stats
        uint64_t nodes_updated_expire{0};
        uint64_t nreads_expire{0};

        TrieUpdateCollectedStats
        delta_since(TrieUpdateCollectedStats const &base) const noexcept;
    };

    static_assert(sizeof(TrieUpdateCollectedStats) == 160);
    static_assert(alignof(TrieUpdateCollectedStats) == 8);
    static_assert(std::is_trivially_copyable_v<TrieUpdateCollectedStats>);
}

MONAD_MPT_NAMESPACE_END
