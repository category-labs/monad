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

#include <cstddef>
#include <cstdint>

// A table of the keccak inputs of 20, 32 and 64 bytes the guest hashes most
// often -- trie keys, mapping slots, log addresses and topics, recovered
// public keys -- each with its keccak computed when the table was built. An
// input found in it is a few word compares instead of a Keccak-f permutation.

namespace monad::zkvm
{
    // The hash first, so that both fields are 8-aligned.
    template <size_t N>
    struct alignas(8) KnownInput
    {
        unsigned char hash[32];
        unsigned char in[N];
    };

#include <zkvm/guest/known_inputs.inc>

    namespace known_input
    {
        [[gnu::always_inline]] inline uint64_t
        word(unsigned char const *const p) noexcept
        {
            uint64_t v;
            __builtin_memcpy(&v, p, 8);
            return v;
        }

        [[gnu::always_inline]] inline uint64_t
        half(unsigned char const *const p) noexcept
        {
            uint32_t v;
            __builtin_memcpy(&v, p, 4);
            return v;
        }

        [[gnu::always_inline]] inline unsigned
        place(uint64_t const fold, unsigned const bits) noexcept
        {
            return static_cast<unsigned>(
                (fold * 0x9E3779B97F4A7C15ull) >> (64 - bits));
        }

        [[gnu::always_inline]] inline void
        take(unsigned char const (&hash)[32], uint8_t *const out) noexcept
        {
            __builtin_memcpy(out, hash, 32);
        }
    }

    // The keccak of the len bytes at in into out, when they are a known
    // input. The fold only places an entry; equality is on every word.
    inline bool known_input_hash(
        unsigned char const *const in, size_t const len,
        uint8_t *const out) noexcept
    {
        using namespace known_input;
        if (len == 32) {
            uint64_t const w0 = word(in), w1 = word(in + 8),
                           w2 = word(in + 16), w3 = word(in + 24);
            unsigned const mask = (1u << KNOWN_32_BITS) - 1;
            for (unsigned s = place(w0 ^ w1 ^ w2 ^ w3, KNOWN_32_BITS);;
                 s = (s + 1) & mask) {
                unsigned const n = known_32_index[s];
                if (n == 0) {
                    return false;
                }
                KnownInput<32> const &e = known_32[n - 1];
                if (word(e.in + 24) == w3 && word(e.in) == w0 &&
                    word(e.in + 8) == w1 && word(e.in + 16) == w2) {
                    take(e.hash, out);
                    return true;
                }
            }
        }
        if (len == 64) {
            uint64_t const w1 = word(in + 8), w2 = word(in + 16),
                           w3 = word(in + 24), w7 = word(in + 56);
            unsigned const mask = (1u << KNOWN_64_BITS) - 1;
            for (unsigned s = place(w1 ^ w2 ^ w3 ^ w7, KNOWN_64_BITS);;
                 s = (s + 1) & mask) {
                unsigned const n = known_64_index[s];
                if (n == 0) {
                    return false;
                }
                KnownInput<64> const &e = known_64[n - 1];
                if (word(e.in + 56) == w7 && word(e.in + 24) == w3 &&
                    word(e.in + 16) == w2 && word(e.in + 8) == w1 &&
                    word(e.in) == word(in) &&
                    word(e.in + 32) == word(in + 32) &&
                    word(e.in + 40) == word(in + 40) &&
                    word(e.in + 48) == word(in + 48)) {
                    take(e.hash, out);
                    return true;
                }
            }
        }
        if (len == 20) {
            uint64_t const w0 = word(in), w1 = word(in + 8),
                           w2 = half(in + 16);
            unsigned const mask = (1u << KNOWN_20_BITS) - 1;
            for (unsigned s = place(w0 ^ w1 ^ w2, KNOWN_20_BITS);;
                 s = (s + 1) & mask) {
                unsigned const n = known_20_index[s];
                if (n == 0) {
                    return false;
                }
                KnownInput<20> const &e = known_20[n - 1];
                if (word(e.in) == w0 && word(e.in + 8) == w1 &&
                    half(e.in + 16) == w2) {
                    take(e.hash, out);
                    return true;
                }
            }
        }
        return false;
    }
}
