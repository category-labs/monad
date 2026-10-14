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

#include <cstddef>
#include <cstdint>

// A table of bytecodes the guest knows, with their keccak computed when the
// table was built. A witness code that is a byte-for-byte copy of an entry
// takes the entry's hash: one DMA compare instead of hashing the code, one
// Keccak-f permutation per 136 bytes.

namespace monad::zkvm
{
    struct KnownCode
    {
        uint32_t size;
        uint32_t offset; // bytes into known_code_words
        uint64_t key;
        unsigned char hash[32];
    };

#include <zkvm/guest/known_codes.inc>

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

    // The keccak of the size bytes at code, 8-aligned, when they are a known
    // code. The key reads the first word and the middle one, both whole for a
    // code of 16 bytes or more; the table holds no shorter code.
    inline bool known_code_hash(
        unsigned char const *const code, size_t const size,
        bytes32_t &hash) noexcept
    {
        if (size < 16) {
            return false;
        }
        uint64_t w0;
        uint64_t wm;
        __builtin_memcpy(&w0, code, 8);
        __builtin_memcpy(&wm, code + 8 * ((size / 8) / 2), 8);
        uint64_t const key = w0 ^ wm;
        unsigned slot = static_cast<unsigned>(
            ((key ^ size) * 0x9E3779B97F4A7C15ull) >>
            (64 - KNOWN_CODE_SLOTS_LOG2));
        for (;;) {
            unsigned const n = known_code_index[slot];
            if (n == 0) {
                return false;
            }
            KnownCode const &e = known_codes[n - 1];
            if (e.size == size && e.key == key &&
                dma_bytes_equal(
                    code,
                    reinterpret_cast<unsigned char const *>(known_code_words) +
                        e.offset,
                    size)) {
                __builtin_memcpy(hash.bytes, e.hash, 32);
                return true;
            }
            slot = (slot + 1) & ((1u << KNOWN_CODE_SLOTS_LOG2) - 1);
        }
    }
}
