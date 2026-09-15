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

#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/monad/db/cache_pricing.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <functional>
#include <map>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class CacheRingKind : uint8_t
{
    accounts,
    storage
};
enum class CacheRingPart : uint8_t
{
    cursor,
    records
};

struct CacheRingConfig
{
    CacheRingKind kind;
    uint32_t records_per_index;
    uint32_t indices;
    uint64_t capacity;
    uint64_t renewal;
};

inline constexpr CacheRingConfig ACCOUNT_RING{
    CacheRingKind::accounts,
    192,
    32768,
    CACHE_ACCOUNT_CAPACITY,
    CACHE_ACCOUNT_RENEWAL};
inline constexpr CacheRingConfig STORAGE_RING{
    CacheRingKind::storage,
    64,
    81920,
    CACHE_STORAGE_CAPACITY,
    CACHE_STORAGE_RENEWAL};
inline constexpr size_t STAMP_LOG_PAGE_BYTES = 4096;
inline constexpr size_t CACHE_RING_HEADER_BYTES = 64;

struct CacheRingCursor
{
    CacheRingView view;
    uint64_t total_charge{0};
    uint64_t floor_charge{0};
    bool operator==(CacheRingCursor const &) const = default;
};

struct CacheRingRecord
{
    // Account records use the first 20 bytes. Storage records use all 60.
    StorageKey key;
    uint8_t weight{1};
    bool deleted{false};
};

struct CacheRingChunk
{
    uint64_t generation{0};
    uint64_t begin_charge{0};
    uint64_t charge{0};
    std::vector<CacheRingRecord> records;
};

using CachePageReader =
    std::function<std::optional<storage_page_t>(bytes32_t const &)>;
using CachePageUpdates = std::map<bytes32_t, storage_page_t>;

bytes32_t
cache_ring_key(CacheRingConfig const &, CacheRingPart, uint64_t generation = 0);
storage_page_t
encode_cache_cursor(CacheRingConfig const &, CacheRingCursor const &);
CacheRingCursor
decode_cache_cursor(CacheRingConfig const &, storage_page_t const &);
storage_page_t
encode_cache_chunk(CacheRingConfig const &, CacheRingChunk const &);
CacheRingChunk decode_cache_chunk(
    CacheRingConfig const &, storage_page_t const &, uint64_t generation);
CacheRingCursor
read_cache_cursor(CacheRingConfig const &, CachePageReader const &);

// A block-local writer reads its parent trie and coalesces changes per page.
// Stamps encode both the logical index and record offset. Deletions mark the
// record in its existing chunk as a weighted tombstone, avoiding a bitmap
// page and preserving the original capacity charge.
class CacheRingWriter
{
    CacheRingConfig config_;
    CachePageReader reader_;
    CacheRingCursor cursor_;
    CachePageUpdates updates_;
    std::map<uint64_t, CacheRingChunk> chunks_;
    bool changed_{false};
    bool cursor_changed_{false};

    CacheRingChunk &chunk(uint64_t generation);
    void advance_boundaries();

public:
    CacheRingWriter(CacheRingConfig config, CachePageReader reader);
    uint64_t append(CacheRingRecord const &);
    bool erase(uint64_t stamp);

    CacheRingView const &view() const
    {
        return cursor_.view;
    }

    CacheRingCursor const &cursor() const
    {
        return cursor_;
    }

    CachePageUpdates finish();
    // Both rings finish into the same block update map. Their three-word
    // cursor regions are merged into one shared metadata page.
    void finish(CachePageUpdates &);
};

// Visit every record still in the protocol range, including tombstones.
// Consumers must let a tombstone override older selections of its key.
void visit_cache_ring(
    CacheRingConfig const &, CachePageReader const &,
    std::function<void(CacheRingRecord const &, uint64_t, bool)> const &);

// Rare fallback when the proposal cache no longer contains the ancestry.
// Fold the authoritative log for one key, retaining last-writer semantics.
uint64_t resolve_cache_stamp(
    CacheRingConfig const &, CachePageReader const &, StorageKey const &);

MONAD_NAMESPACE_END
