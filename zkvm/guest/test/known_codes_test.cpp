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

// The guest trusts each known code's hash: check that it is the keccak of
// the entry's bytes, and that the index finds every entry under its key.

#include <zkvm/guest/known_codes.hpp>

#include <category/crypto/keccak.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>

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
    for (size_t n = 0; n < count; ++n) {
        KnownCode const &e = known_codes[n];
        unsigned char const *const code = base + e.offset;
        require(e.size >= 16, "shorter than 16 bytes", n);
        require(
            e.offset + e.size <= sizeof(known_code_words), "past the words", n);
        unsigned char hash[32];
        monad_keccak256(code, e.size, hash);
        require(
            std::memcmp(hash, e.hash, 32) == 0,
            "hash is not the keccak of its bytes",
            n);
        require(known_code_key(code, e.size) == e.key, "wrong key", n);
        unsigned slot = known_code_slot(e.key, e.size);
        while (known_code_index[slot] != n + 1) {
            require(known_code_index[slot] != 0, "not in the index", n);
            slot = (slot + 1) & ((1u << KNOWN_CODE_SLOTS_LOG2) - 1);
        }
    }
    std::printf("Known codes: %zu hashes and index entries checked\n", count);
}
