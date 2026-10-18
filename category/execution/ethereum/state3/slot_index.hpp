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

// A linear scan visits a few entries. With the ZisK guest's -funroll-loops,
// gcc enters the eight-way unrolled copy through a chain of compares on the
// trip count's remainder, two steps a case: dearer than the loop tests the
// unrolling saves. The Airbender guest is built the same way.
#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_AIRBENDER)
    #define MONAD_SLOT_SCAN _Pragma("GCC unroll 1")
#else
    #define MONAD_SLOT_SCAN
#endif

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
// Check word 3 first: it differs between small slot numbers, whose word 0 is
// zero, and between keccak-derived keys alike. Then words 0, 1 and 2 to
// confirm equality.
[[nodiscard]] inline bool
key_equals(bytes32_t const &k, std::uint64_t const tail, bytes32_t const &e)
{
    std::uint64_t a, b;
    __builtin_memcpy(&a, e.bytes + 24, 8);
    if (a != tail) {
        return false;
    }
#ifdef MONAD_ZKVM_ZISK
    // A tail that matches is nearly always the key: the other three words by
    // the DMA comparator (CSR 0x814, the length in the flag after it), one
    // step and the words it reads, where they cost three steps each.
    std::uint64_t differ;
    __asm__(".option push\n\t"
            ".option arch, +zicsr\n\t"
            "csrrs %0, 0x814, %1\n\t"
            "addi x0, %2, 24\n\t"
            ".option pop"
            : "=&r"(differ)
            : "r"(e.bytes),
              "r"(k.bytes),
              "m"(*reinterpret_cast<unsigned char const(*)[24]>(e.bytes)),
              "m"(*reinterpret_cast<unsigned char const(*)[24]>(k.bytes)));
    (void)b;
    return differ == 0;
#elif defined(MONAD_ZKVM_AIRBENDER)
    // No unaligned access on rv32: 32-bit words when both keys are
    // word-aligned, as the vector entries and nearly every search key are.
    (void)b;
    if (((reinterpret_cast<std::uintptr_t>(k.bytes) |
          reinterpret_cast<std::uintptr_t>(e.bytes)) &
         3) == 0) {
        auto const *const x = static_cast<unsigned char const *>(
            __builtin_assume_aligned(k.bytes, 4));
        auto const *const y = static_cast<unsigned char const *>(
            __builtin_assume_aligned(e.bytes, 4));
        std::uint32_t diff = 0;
        for (std::size_t i = 0; i < 24; i += 4) {
            std::uint32_t u, v;
            __builtin_memcpy(&u, x + i, 4);
            __builtin_memcpy(&v, y + i, 4);
            diff |= u ^ v;
        }
        return diff == 0;
    }
    return __builtin_memcmp(k.bytes, e.bytes, 24) == 0;
#else
    __builtin_memcpy(&a, e.bytes, 8);
    __builtin_memcpy(&b, k.bytes, 8);
    if (a != b) {
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
#endif
}

#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_AIRBENDER)
// Optional index for vectors of slot keys or (key, value) pairs.
// Copies omit this derived cache; moves transfer it with the owning vector.
class SlotIndex
{
    struct Table
    {
        std::vector<std::uint32_t> slots; // Position + 1; 0 means empty.
        std::size_t mask{};
        unsigned shift{}; // 64 - log2(slots.size()).
    };

    std::unique_ptr<Table> table_{};
#if defined(MONAD_ZKVM_AIRBENDER)
    static constexpr std::size_t index_from = 4;
#else
    static constexpr std::size_t index_from = 16;
#endif

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
        // On little-endian targets, key_tail places small big-endian slot
        // numbers in the high bits. Use those bits to avoid clustering them
        // in bucket 0; keccak-derived keys are uniform either way.
        std::size_t h =
            static_cast<std::size_t>(key_tail(key) >> table_->shift);
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
        table_->shift = 64u - static_cast<unsigned>(std::bit_width(cap) - 1);
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
        std::size_t h = static_cast<std::size_t>(tail >> table_->shift);
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
