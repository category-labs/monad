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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>

#include <cstdint>

// The keccak of a trie key's preimage -- an address or a storage slot --
// from a table of the ones most often read, each with its hash computed when
// the table was built; any other is hashed. A table hit costs a few word
// compares where a hash costs a Keccak-f permutation.

MONAD_NAMESPACE_BEGIN

#if defined(MONAD_ZKVM_ZISK)
namespace known_keys
{
    // The hash first, so that both fields are 8-aligned.
    struct alignas(8) KnownAddress
    {
        unsigned char hash[32];
        unsigned char pre[20];
    };

    struct alignas(8) KnownSlot
    {
        unsigned char hash[32];
        unsigned char pre[32];
    };

    #include <category/execution/ethereum/db/known_keys.inc>

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

    [[gnu::always_inline]] inline monad_hash256
    hash_of(unsigned char const (&h)[32]) noexcept
    {
        monad_hash256 r;
        __builtin_memcpy(r.bytes, h, 32);
        return r;
    }

    // Where a preimage's words, folded, place it in an index of 2^bits.
    [[gnu::always_inline]] inline unsigned
    place(uint64_t const fold, unsigned const bits) noexcept
    {
        return static_cast<unsigned>(
            (fold * 0x9E3779B97F4A7C15ull) >> (64 - bits));
    }
}
#endif

inline monad_hash256 key_hash(Address const &a) noexcept
{
#if defined(MONAD_ZKVM_ZISK)
    using namespace known_keys;
    uint64_t const w0 = word(a.bytes);
    uint64_t const w1 = word(a.bytes + 8);
    uint64_t const w2 = half(a.bytes + 16);
    unsigned const mask = (1u << KNOWN_ADDRESS_SLOTS_LOG2) - 1;
    for (unsigned s = place(w0 ^ w1 ^ w2, KNOWN_ADDRESS_SLOTS_LOG2);;
         s = (s + 1) & mask) {
        unsigned const n = known_address_index[s];
        if (n == 0) {
            break;
        }
        KnownAddress const &e = known_addresses[n - 1];
        if (word(e.pre) == w0 && word(e.pre + 8) == w1 &&
            half(e.pre + 16) == w2) {
            return hash_of(e.hash);
        }
    }
#endif
    return keccak256(a.bytes);
}

inline monad_hash256 key_hash(bytes32_t const &k) noexcept
{
#if defined(MONAD_ZKVM_ZISK)
    using namespace known_keys;
    uint64_t const w0 = word(k.bytes);
    uint64_t const w1 = word(k.bytes + 8);
    uint64_t const w2 = word(k.bytes + 16);
    uint64_t const w3 = word(k.bytes + 24);
    unsigned const mask = (1u << KNOWN_SLOT_SLOTS_LOG2) - 1;
    for (unsigned s = place(w0 ^ w1 ^ w2 ^ w3, KNOWN_SLOT_SLOTS_LOG2);;
         s = (s + 1) & mask) {
        unsigned const n = known_slot_index[s];
        if (n == 0) {
            break;
        }
        KnownSlot const &e = known_slots[n - 1];
        if (word(e.pre + 24) == w3 && word(e.pre) == w0 &&
            word(e.pre + 8) == w1 && word(e.pre + 16) == w2) {
            return hash_of(e.hash);
        }
    }
#endif
    return keccak256(k.bytes);
}

MONAD_NAMESPACE_END
