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

#include <bit>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

// Keep short slot scans rolled on ZisK to avoid unrolling overhead.
#ifdef MONAD_ZKVM_ZISK
    #define MONAD_SLOT_SCAN _Pragma("GCC unroll 1")
#else
    #define MONAD_SLOT_SCAN
#endif

MONAD_NAMESPACE_BEGIN

// Preload the key's last word for linear scans. Small big-endian keys differ
// there; preloading all four words measured worse.
[[nodiscard]] inline std::uint64_t key_tail(bytes32_t const &key)
{
    std::uint64_t last_word;
    __builtin_memcpy(&last_word, key.bytes + 24, 8);
    // Keep the tail load outside the scan and prevent GCC from folding the
    // comparisons back into an address-order memcmp. Not a memory barrier.
    __asm__("" : "+r"(last_word));
    return last_word;
}

// Compare key with entry_key; tail must be key_tail(key).
// Check the last word first: small slot numbers differ there.
// Compare the remaining words only if it matches.
[[nodiscard]] inline bool key_equals(
    bytes32_t const &key, std::uint64_t const tail, bytes32_t const &entry_key)
{
    std::uint64_t entry_word, key_word;
    __builtin_memcpy(&entry_word, entry_key.bytes + 24, 8);
    if (entry_word != tail) {
        return false;
    }
#ifdef MONAD_ZKVM_ZISK
    // Compare the remaining 24 bytes with ZisK DMA (CSR 0x814).
    // The following addi encodes the second pointer and length.
    std::uint64_t different;
    __asm__(
        ".option push\n\t"
        ".option arch, +zicsr\n\t"
        "csrrs %0, 0x814, %1\n\t"
        "addi x0, %2, 24\n\t"
        ".option pop"
        : "=&r"(different)
        : "r"(entry_key.bytes),
          "r"(key.bytes),
          "m"(*reinterpret_cast<unsigned char const(*)[24]>(entry_key.bytes)),
          "m"(*reinterpret_cast<unsigned char const(*)[24]>(key.bytes)));
    (void)key_word;
    return different == 0;
#else
    __builtin_memcpy(&entry_word, entry_key.bytes, 8);
    __builtin_memcpy(&key_word, key.bytes, 8);
    if (entry_word != key_word) {
        return false;
    }
    __builtin_memcpy(&entry_word, entry_key.bytes + 8, 8);
    __builtin_memcpy(&key_word, key.bytes + 8, 8);
    if (entry_word != key_word) {
        return false;
    }
    __builtin_memcpy(&entry_word, entry_key.bytes + 16, 8);
    __builtin_memcpy(&key_word, key.bytes + 16, 8);
    return entry_word == key_word;
#endif
}

#ifdef MONAD_ZKVM_ZISK
// Optional index for vectors of slot keys or (key, value) pairs.
// Copies discard this derived index and fall back to linear lookup.
// Moves transfer the index along with the owning vector.
class SlotIndex
{
    struct Table
    {
        std::vector<std::uint32_t> slots; // Position + 1; 0 means empty.
        std::size_t bucket_mask{};
        unsigned bucket_shift{}; // 64 - log2(slots.size()).
    };

    std::unique_ptr<Table> table_{};
    static constexpr std::size_t MIN_INDEXED_ENTRIES = 16;

    static bytes32_t const &key_of(bytes32_t const &entry)
    {
        return entry;
    }

    static bytes32_t const &key_of(std::pair<bytes32_t, bytes32_t> const &entry)
    {
        return entry.first;
    }

    [[gnu::always_inline]] inline void
    insert(std::size_t const entry_position, bytes32_t const &key)
    {
        // On little-endian targets, key_tail places small big-endian slot
        // numbers in the high bits. Use those bits to avoid clustering them
        // in bucket 0; keccak-derived keys are uniform either way.
        std::size_t bucket =
            static_cast<std::size_t>(key_tail(key) >> table_->bucket_shift);
        // on_insert keeps the table at most half full, so probing terminates.
        while (table_->slots[bucket] != 0) {
            bucket = (bucket + 1) & table_->bucket_mask;
        }
        table_->slots[bucket] = static_cast<std::uint32_t>(entry_position + 1);
    }

    template <typename Entry>
    void rebuild(std::size_t const size, std::vector<Entry> const &entries)
    {
        // A power of two makes masking equivalent to modulo capacity.
        std::size_t capacity = 32;
        while (capacity < size * 2) {
            capacity *= 2;
        }
        if (!table_) {
            table_ = std::make_unique<Table>();
        }
        table_->slots.assign(capacity, 0);
        table_->bucket_mask = capacity - 1;
        table_->bucket_shift =
            64u - static_cast<unsigned>(std::bit_width(capacity) - 1);
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

    // Call after appending an entry. Inline the no-op path when no index
    // exists and the vector is still below MIN_INDEXED_ENTRIES.
    template <typename Entry>
    [[gnu::always_inline]] inline void
    on_insert(std::vector<Entry> const &entries)
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
        else if (size >= MIN_INDEXED_ENTRIES) {
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
        std::size_t bucket =
            static_cast<std::size_t>(tail >> table_->bucket_shift);
        for (;;) {
            std::uint32_t const position_plus_one = table_->slots[bucket];
            if (position_plus_one == 0 ||
                key_equals(key, tail, key_of(entries[position_plus_one - 1]))) {
                return position_plus_one;
            }
            bucket = (bucket + 1) & table_->bucket_mask;
        }
    }
};
#endif

MONAD_NAMESPACE_END
