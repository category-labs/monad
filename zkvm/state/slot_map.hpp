// Copyright (C) 2025-26 Category Labs, Inc.
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

// A map from slot key to row, for the slots of one account. Rows live in a
// vector in creation order and are only ever appended, never erased or
// reordered, until the whole map is cleared. Most accounts touch a handful
// of slots, so the vector is scanned while it is short: slot keys are mostly
// small big-endian numbers, and comparing the last word first rejects nearly
// every non-match on its own. From SLOT_INDEX_FROM entries the map keeps an
// open-addressing index bucketed by the seeded full-key hash (see
// key_hash.hpp). The tail word alone would not do for the index: keys that
// share a tail and differ higher up collide under every seed, and a contract
// chooses its own slot keys.

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <zkvm/state/key_hash.hpp>

#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace zkvm
{
    // The key's last word, loaded once per lookup.
    [[nodiscard]] [[gnu::always_inline]] inline uint64_t
    key_tail(bytes32_t const &k) noexcept
    {
        uint64_t w;
        std::memcpy(&w, k.bytes + 24, 8);
        return w;
    }

    // Whether entry key `e` equals the search key `k`, given tail ==
    // key_tail(k). The tail is compared first and the remaining three words
    // only if it matches.
    [[nodiscard]] [[gnu::always_inline]] inline bool
    key_equals(bytes32_t const &k, uint64_t const tail, bytes32_t const &e)
    {
        uint64_t a;
        std::memcpy(&a, e.bytes + 24, 8);
        if (a != tail) {
            return false;
        }
        return std::memcmp(k.bytes, e.bytes, 24) == 0;
    }

    // Entry count at which the index is built.
    inline constexpr size_t SLOT_INDEX_FROM = 16;

    // Capacity reserved by the first insertion. The guest's arena never
    // frees, so every doubling abandons the old buffer: a floor trades a
    // little memory for no copies on the common small maps.
    inline constexpr size_t SLOT_RESERVE = 16;

    // Entries must expose a `key` member and be default constructible. The
    // map keys its index with the State's seed, which outlives every row.
    template <class Entry>
    class SlotMap
    {
        KeySeed const &seed_;
        std::vector<Entry> entries_;
        // Position + 1 of each entry, 0 for an empty bucket; empty until
        // the map is indexed. Capacity is a power of two at least twice the
        // entry count, so a probe always terminates.
        std::vector<uint32_t> table_;
        uint64_t mask_{0};
        unsigned shift_{0};

        [[nodiscard]] bool indexed() const noexcept
        {
            return !table_.empty();
        }

        [[gnu::always_inline]] inline void index_insert(size_t const pos)
        {
            uint64_t h = hash_bytes32(entries_[pos].key, seed_) >> shift_;
            while (table_[h] != 0) {
                h = (h + 1) & mask_;
            }
            table_[h] = static_cast<uint32_t>(pos + 1);
        }

        void index_rebuild()
        {
            size_t cap = 2 * SLOT_INDEX_FROM;
            while (cap < 2 * entries_.size()) {
                cap *= 2;
            }
            table_.assign(cap, 0);
            mask_ = cap - 1;
            shift_ = 64u - static_cast<unsigned>(std::bit_width(cap) - 1);
            for (size_t i = 0; i < entries_.size(); ++i) {
                index_insert(i);
            }
        }

        [[nodiscard]] [[gnu::always_inline]] inline Entry const *
        find_impl(bytes32_t const &key) const
        {
            uint64_t const tail = key_tail(key);
            if (indexed()) {
                uint64_t h = hash_bytes32(key, seed_) >> shift_;
                for (;;) {
                    uint32_t const p = table_[h];
                    if (p == 0) {
                        return nullptr;
                    }
                    if (key_equals(key, tail, entries_[p - 1].key)) {
                        return &entries_[p - 1];
                    }
                    h = (h + 1) & mask_;
                }
            }
            for (Entry const &e : entries_) {
                if (key_equals(key, tail, e.key)) {
                    return &e;
                }
            }
            return nullptr;
        }

    public:
        explicit SlotMap(KeySeed const &seed) noexcept
            : seed_{seed}
        {
        }

        // The entry for `key`, or nullptr.
        [[nodiscard]] [[gnu::always_inline]] inline Entry *
        find(bytes32_t const &key)
        {
            return const_cast<Entry *>(find_impl(key));
        }

        [[nodiscard]] [[gnu::always_inline]] inline Entry const *
        find(bytes32_t const &key) const
        {
            return find_impl(key);
        }

        // Append a default entry for `key`, which must be absent. Pointers
        // to earlier entries may be invalidated by the vector's growth;
        // positions never are.
        Entry &emplace(bytes32_t const &key)
        {
            MONAD_DEBUG_ASSERT(find(key) == nullptr);
            if (entries_.capacity() == 0) {
                entries_.reserve(SLOT_RESERVE);
            }
            Entry &e = entries_.emplace_back();
            e.key = key;
            size_t const size = entries_.size();
            if (indexed()) {
                if (table_.size() < 2 * size) {
                    index_rebuild();
                }
                else {
                    index_insert(size - 1);
                }
            }
            else if (size >= SLOT_INDEX_FROM) {
                index_rebuild();
            }
            return e;
        }

        // Entries by position, which never changes while the map lives:
        // what the journal records instead of a pointer.
        [[nodiscard]] size_t index_of(Entry const &e) const noexcept
        {
            return static_cast<size_t>(&e - entries_.data());
        }

        [[nodiscard]] Entry &at(size_t const pos) noexcept
        {
            MONAD_DEBUG_ASSERT(pos < entries_.size());
            return entries_[pos];
        }

        // Drop every entry. Both buffers keep their capacity.
        void clear() noexcept
        {
            entries_.clear();
            table_.clear();
        }

        [[nodiscard]] size_t size() const noexcept
        {
            return entries_.size();
        }

        [[nodiscard]] bool empty() const noexcept
        {
            return entries_.empty();
        }

        [[nodiscard]] auto begin() noexcept
        {
            return entries_.begin();
        }

        [[nodiscard]] auto end() noexcept
        {
            return entries_.end();
        }

        [[nodiscard]] auto begin() const noexcept
        {
            return entries_.begin();
        }

        [[nodiscard]] auto end() const noexcept
        {
            return entries_.end();
        }
    };
}

MONAD_NAMESPACE_END
