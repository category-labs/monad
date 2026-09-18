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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Preload the key's last word for linear scans. Small big-endian keys differ
// there; preloading all four words measured worse.
[[nodiscard]] inline std::uint64_t key_tail(bytes32_t const &k)
{
    std::uint64_t w;
    __builtin_memcpy(&w, k.bytes + 24, 8);
    // Keep the tail load outside the scan and prevent GCC from folding the
    // comparisons back into an address-order memcmp. Not a memory barrier.
    __asm__("" : "+r"(w));
    return w;
}

// Compare search key k with entry key e; tail must be key_tail(k).
// Check words 0 and 3 first to reject most mismatches early,
// then words 1 and 2 to confirm equality.
[[nodiscard]] inline bool
key_equals(bytes32_t const &k, std::uint64_t const tail, bytes32_t const &e)
{
    std::uint64_t a, b;
    __builtin_memcpy(&a, e.bytes, 8);
    __builtin_memcpy(&b, k.bytes, 8);
    if (a != b) {
        return false;
    }
    __builtin_memcpy(&a, e.bytes + 24, 8);
    if (a != tail) {
        return false;
    }
    __builtin_memcpy(&a, e.bytes + 8, 8);
    __builtin_memcpy(&b, k.bytes + 8, 8);
    if (a != b) {
        return false;
    }
    __builtin_memcpy(&a, e.bytes + 16, 8);
    __builtin_memcpy(&b, k.bytes + 16, 8);
    return a == b;
}

#ifdef MONAD_ZKVM_ZISK
// Optional index for vectors of slot keys or (key, value) pairs.
// Copies omit this derived cache; moves transfer it with the owning vector.
class SlotIndex
{
    struct Table
    {
        std::vector<std::uint32_t> slots; // Position + 1; 0 means empty.
        std::size_t mask{};
    };

    std::unique_ptr<Table> table_{};
    static constexpr std::size_t index_from = 16;

    static bytes32_t const &key_of(bytes32_t const &entry)
    {
        return entry;
    }

    static bytes32_t const &key_of(std::pair<bytes32_t, bytes32_t> const &entry)
    {
        return entry.first;
    }

    [[gnu::always_inline]] inline void
    insert(std::size_t const pos, bytes32_t const &key)
    {
        std::size_t h = static_cast<std::size_t>(key_tail(key)) & table_->mask;
        // on_insert keeps the table at most half full, so probing terminates.
        while (table_->slots[h] != 0) {
            h = (h + 1) & table_->mask;
        }
        table_->slots[h] = static_cast<std::uint32_t>(pos + 1);
    }

    template <typename Entry>
    void rebuild(std::size_t const size, std::vector<Entry> const &entries)
    {
        // A power of two makes masking equivalent to modulo capacity.
        std::size_t cap = 32;
        while (cap < size * 2) {
            cap *= 2;
        }
        if (!table_) {
            table_ = std::make_unique<Table>();
        }
        table_->slots.assign(cap, 0);
        table_->mask = cap - 1;
        for (std::size_t i = 0; i < size; ++i) {
            insert(i, key_of(entries[i]));
        }
    }

public:
    SlotIndex() = default;

    SlotIndex(SlotIndex const &) noexcept {}

    SlotIndex &operator=(SlotIndex const &) noexcept
    {
        reset();
        return *this;
    }

    SlotIndex(SlotIndex &&) noexcept = default;
    SlotIndex &operator=(SlotIndex &&) noexcept = default;

    [[nodiscard]] explicit operator bool() const noexcept
    {
        return static_cast<bool>(table_);
    }

    // Call after appending one entry to the vector.
    template <typename Entry>
    void on_insert(std::vector<Entry> const &entries)
    {
        std::size_t const size = entries.size();
        if (table_) {
            if (table_->slots.size() < size * 2) {
                rebuild(size, entries);
            }
            else {
                insert(size - 1, key_of(entries[size - 1]));
            }
        }
        else if (size >= index_from) {
            rebuild(size, entries);
        }
    }

    // Invalidate after removing or moving entries in the owning vector.
    void reset() noexcept
    {
        table_.reset();
    }

    // Requires an active index. Return position + 1, or zero if absent.
    template <typename Entry>
    [[nodiscard]] [[gnu::always_inline]] inline std::uint32_t lookup(
        bytes32_t const &key, std::uint64_t const tail,
        std::vector<Entry> const &entries) const
    {
        std::size_t h = static_cast<std::size_t>(tail) & table_->mask;
        for (;;) {
            std::uint32_t const p = table_->slots[h];
            if (p == 0 || key_equals(key, tail, key_of(entries[p - 1]))) {
                return p;
            }
            h = (h + 1) & table_->mask;
        }
    }
};
#endif

MONAD_NAMESPACE_END
