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
#include <category/mpt/util.hpp>

#include <cstdint>
#include <type_traits>

MONAD_MPT_NAMESPACE_BEGIN

enum class timeline_id : uint8_t
{
    primary = 0,
    secondary = 1
};

static constexpr unsigned NUM_TIMELINES = 2;
static_assert(
    static_cast<unsigned>(timeline_id::secondary) + 1 == NUM_TIMELINES);

/// Per-timeline compaction state. Each timeline maintains its own compaction
/// boundary and stride. Disk growth tracking remains global since both
/// timelines share the same fast/slow append rings.
struct timeline_compaction_state
{
    compact_offset_pair compact_offsets{
        MIN_COMPACT_VIRTUAL_OFFSET, MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t compact_offset_range_fast_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    compact_virtual_chunk_offset_t compact_offset_range_slow_{
        MIN_COMPACT_VIRTUAL_OFFSET};
    int64_t curr_upsert_auto_expire_version{0};
};

static_assert(std::is_trivially_copyable_v<timeline_compaction_state>);

MONAD_MPT_NAMESPACE_END
