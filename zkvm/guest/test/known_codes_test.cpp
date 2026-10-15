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

// The guest trusts each known code's hash, JUMPDEST map and padding: check
// that the hash is the keccak of the entry's bytes, that the map is the
// interpreter's analysis of them, that the bytes stand between Intercode's
// padding (32 zero bytes before, 33 after), that the index finds every
// entry under its key, and that an entry's sibling word lies inside it.

#include <zkvm/guest/known_codes.hpp>

#include <category/crypto/keccak.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

namespace
{
    void require(bool const ok, char const *const what, size_t const n)
    {
        if (!ok) {
            std::fprintf(stderr, "known code %zu: %s\n", n, what);
            std::exit(1);
        }
    }
}

int main()
{
    using namespace monad::zkvm;
    auto const *const base =
        reinterpret_cast<unsigned char const *>(known_code_words);
    size_t const count = sizeof(known_codes) / sizeof(known_codes[0]);
    static_assert(
        sizeof(known_code_sibling_word) / sizeof(known_code_sibling_word[0]) ==
        sizeof(known_codes) / sizeof(known_codes[0]));
    for (size_t n = 0; n < count; ++n) {
        KnownCode const &e = known_codes[n];
        unsigned char const *const code = base + e.offset;
        require(e.size >= 16, "shorter than 16 bytes", n);
        require(
            e.offset >= 32 &&
                e.offset + e.size + 33 <= sizeof(known_code_words),
            "padding past the words",
            n);
        for (size_t i = 1; i <= 32; ++i) {
            require(code[-static_cast<ptrdiff_t>(i)] == 0, "padding before", n);
        }
        for (size_t i = 0; i < 33; ++i) {
            require(code[e.size + i] == 0, "padding after", n);
        }
        require(e.offset % 8 == 0, "unaligned", n);
        unsigned char hash[32];
        monad_keccak256(code, e.size, hash);
        require(
            std::memcmp(hash, e.hash, 32) == 0,
            "hash is not the keccak of its bytes",
            n);
        require(known_code_key(code, e.size) == e.key, "wrong key", n);
        uint32_t const j = known_code_sibling_word[n];
        require(
            j == NO_SIBLING_WORD || 8 * size_t{j} + 8 <= e.size,
            "sibling word past the code",
            n);
        // Intercode::find_jumpdests' software analysis: a JUMPDEST byte
        // outside any PUSH's immediate data.
        std::vector<uint64_t> map((e.size + 63) / 64, 0);
        for (size_t i = 0; i < e.size;) {
            uint8_t const op = code[i];
            if (op == 0x5b) {
                map[i / 64] |= uint64_t{1} << (i % 64);
            }
            i += 1 + (op >= 0x60 && op <= 0x7f ? op - 0x5f : 0);
        }
        require(
            std::memcmp(
                map.data(),
                known_code_jumpdests + e.jumpdests,
                map.size() * sizeof(uint64_t)) == 0,
            "JUMPDEST map is not the analysis of its bytes",
            n);
        unsigned slot = known_code_slot(e.key, e.size);
        while (known_code_index[slot] != n + 1) {
            require(known_code_index[slot] != 0, "not in the index", n);
            slot = (slot + 1) & ((1u << KNOWN_CODE_SLOTS_LOG2) - 1);
        }
        unsigned hslot = known_code_hash_slot(e.hash);
        while (known_code_hash_index[hslot] != n + 1) {
            require(
                known_code_hash_index[hslot] != 0, "not in the hash index", n);
            hslot = (hslot + 1) & ((1u << KNOWN_CODE_HASH_SLOTS_LOG2) - 1);
        }
    }
    std::printf(
        "Known codes: %zu hashes, JUMPDEST maps and index entries (by key and "
        "by keccak) checked\n",
        count);
}
