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

#if defined(MONAD_ZKVM_ZISK)
    #include <category/vm/code.hpp>
#endif

#include <cstddef>
#include <cstdint>

// A table of bytecodes the guest knows, each padded as Intercode pads a code,
// with its keccak and JUMPDEST map computed when the table was built. A
// witness code that is a byte-for-byte copy of an entry takes the entry's
// hash, copy and map: one DMA compare instead of hashing the code (one
// Keccak-f permutation per 136 bytes), copying it and analysing it.

namespace monad::zkvm
{
    struct KnownCode
    {
        uint32_t size;
        uint32_t offset; // bytes into known_code_words
        uint32_t jumpdests; // words into known_code_jumpdests
        uint64_t key;
        unsigned char hash[32];
    };

#include <zkvm/guest/known_codes.inc>
#include <zkvm/guest/known_codes_ambiguous.inc>
#include <zkvm/guest/known_codes_hash.inc>

    // The key a code is filed under: its first word and its middle one, both
    // whole and 8-aligned in a copy of 16 bytes or more.
    [[gnu::always_inline]] inline uint64_t
    known_code_key(unsigned char const *const code, size_t const size) noexcept
    {
        uint64_t w0;
        uint64_t wm;
        __builtin_memcpy(&w0, code, 8);
        __builtin_memcpy(&wm, code + 8 * ((size / 8) / 2), 8);
        return w0 ^ wm;
    }

    [[gnu::always_inline]] inline unsigned
    known_code_slot(uint64_t const key, size_t const size) noexcept
    {
        return static_cast<unsigned>(
            ((key ^ size) * 0x9E3779B97F4A7C15ull) >>
            (64 - KNOWN_CODE_SLOTS_LOG2));
    }

    // The slot of known_code_hash_index a keccak is probed from: its first
    // word, read little-endian.
    [[gnu::always_inline]] inline unsigned
    known_code_hash_slot(unsigned char const *const hash) noexcept
    {
        uint64_t w0;
        __builtin_memcpy(&w0, hash, 8);
        return static_cast<unsigned>(
            (w0 * 0x9E3779B97F4A7C15ull) >> (64 - KNOWN_CODE_HASH_SLOTS_LOG2));
    }

#if defined(MONAD_ZKVM_ZISK)
    // Whether the size bytes at a and b are equal, by the DMA comparator (CSR
    // 0x814, the length in the register after it).
    [[gnu::always_inline]] inline bool dma_bytes_equal(
        unsigned char const *const a, unsigned char const *const b,
        size_t const size) noexcept
    {
        uint64_t differ;
        asm volatile(".option push\n\t"
                     ".option arch, +zicsr\n\t"
                     "csrrs %0, 0x814, %1\n\t"
                     "add x0, %2, %3\n\t"
                     ".option pop"
                     : "=&r"(differ)
                     : "r"(a), "r"(b), "r"(size)
                     : "memory");
        return differ == 0;
    }

    // The entry the size bytes at code are a copy of, or null. The key reads
    // the first word and the middle one, both whole for a code of 16 bytes or
    // more; the table holds no shorter code. The compare is by DMA, aligned or
    // not.
    inline KnownCode const *
    known_code_find(unsigned char const *const code, size_t const size) noexcept
    {
        if (size < 16) {
            return nullptr;
        }
        uint64_t const key = known_code_key(code, size);
        unsigned slot = known_code_slot(key, size);
        for (;;) {
            unsigned const n = known_code_index[slot];
            if (n == 0) {
                return nullptr;
            }
            KnownCode const &e = known_codes[n - 1];
            if (e.size == size && e.key == key &&
                dma_bytes_equal(
                    code,
                    reinterpret_cast<unsigned char const *>(known_code_words) +
                        e.offset,
                    size)) {
                return &e;
            }
            slot = (slot + 1) & ((1u << KNOWN_CODE_SLOTS_LOG2) - 1);
        }
    }

    // The first entry with the size and key of the size bytes at code, or
    // null: a code that may be its copy, not compared.
    inline KnownCode const *known_code_probable(
        unsigned char const *const code, size_t const size) noexcept
    {
        if (size < 16) {
            return nullptr;
        }
        uint64_t const key = known_code_key(code, size);
        unsigned slot = known_code_slot(key, size);
        for (;;) {
            unsigned const n = known_code_index[slot];
            if (n == 0) {
                return nullptr;
            }
            KnownCode const &e = known_codes[n - 1];
            if (e.size == size && e.key == key) {
                return &e;
            }
            slot = (slot + 1) & ((1u << KNOWN_CODE_SLOTS_LOG2) - 1);
        }
    }

    // Whether another code with e's size and key was seen when the table was
    // learnt: a witness code with them is then compared, not set aside.
    [[gnu::always_inline]] inline bool
    known_code_is_ambiguous(KnownCode const &e) noexcept
    {
        size_t const n = static_cast<size_t>(&e - known_codes);
        return ((known_code_ambiguous[n / 64] >> (n % 64)) & 1) != 0;
    }

    // The entry whose keccak is hash, or null, probed from its first word.
    inline KnownCode const *
    known_code_by_hash(unsigned char const *const hash) noexcept
    {
        constexpr unsigned mask = (1u << KNOWN_CODE_HASH_SLOTS_LOG2) - 1;
        unsigned slot = known_code_hash_slot(hash);
        for (;;) {
            unsigned const n = known_code_hash_index[slot];
            if (n == 0) {
                return nullptr;
            }
            KnownCode const &e = known_codes[n - 1];
            if (__builtin_memcmp(e.hash, hash, 32) == 0) {
                return &e;
            }
            slot = (slot + 1) & mask;
        }
    }

    // A known code's Intercode: the table's padded copy and JUMPDEST map.
    inline vm::SharedIntercode known_code_intercode(KnownCode const &e)
    {
        return vm::make_shared_intercode(
            reinterpret_cast<uint8_t const *>(known_code_words) + e.offset,
            size_t{e.size},
            known_code_jumpdests + e.jumpdests);
    }
#endif
}
