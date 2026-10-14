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

// The guest trusts each known input's hash: check that it is the keccak of
// the input, and that known_input_hash finds every entry and returns it.

#include <zkvm/guest/known_inputs.hpp>

#include <category/crypto/keccak.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace
{
    void require(bool const ok, char const *const what, size_t const n)
    {
        if (!ok) {
            std::fprintf(stderr, "known input %zu: %s\n", n, what);
            std::exit(1);
        }
    }

    template <size_t N, size_t COUNT>
    size_t check(monad::zkvm::KnownInput<N> const (&table)[COUNT])
    {
        for (size_t n = 0; n < COUNT; ++n) {
            auto const &e = table[n];
            unsigned char hash[32];
            monad_keccak256(e.in, N, hash);
            require(
                std::memcmp(hash, e.hash, 32) == 0,
                "hash is not the keccak of its input",
                n);
            // The lookup as the guest makes it, from an unaligned copy.
            alignas(8) unsigned char copy[N + 1];
            std::memcpy(copy + 1, e.in, N);
            uint8_t out[32];
            require(
                monad::zkvm::known_input_hash(copy + 1, N, out),
                "not found",
                n);
            require(std::memcmp(out, e.hash, 32) == 0, "wrong hash found", n);
        }
        return COUNT;
    }
}

int main()
{
    using namespace monad::zkvm;
    size_t const count = check(known_20) + check(known_32) + check(known_64);
    // An input one bit away from a known one is not known.
    alignas(8) unsigned char flipped[64];
    std::memcpy(flipped, known_64[0].in, 64);
    flipped[63] ^= 1;
    uint8_t out[32];
    unsigned char hash[32];
    monad_keccak256(flipped, 64, hash);
    require(
        !known_input_hash(flipped, 64, out) ||
            std::memcmp(out, hash, 32) == 0,
        "a different input took a table hash",
        0);
    std::printf("Known inputs: %zu hashes and lookups checked\n", count);
}
