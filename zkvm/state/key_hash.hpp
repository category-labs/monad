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

// Map-key hashes for the guest state tables.
//
// The host hashes Address and bytes32_t keys with seeded komihash, which is
// general-purpose and HashDoS-hardened. The guest's keys have two fixed
// widths, so a word-wise fold is enough: one 128-bit product per 16 bytes,
// mixed by XOR of its halves, which is a handful of RISC-V instructions and
// was the largest single cycle win measured on the ZisK branch.
//
// The fold is keyed by a KeySeed derived from the block hash, and every
// bucket choice in the guest state goes through it: the row map, the code
// table and the per-account slot indexes. With fixed parameters anyone could
// precompute a set of addresses or slot keys that share a bucket and turn
// each lookup into a scan over all of them, making the block quadratic to
// prove. The block hash commits to the transactions, so the seed is unknown
// while they are chosen, and colliding under one seed says nothing about
// another. This is a prover-liveness guard only: complete keys are compared
// on every probe, so a collision costs time and never changes a result.

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <cstdint>
#include <cstring>

MONAD_NAMESPACE_BEGIN

namespace zkvm
{
    namespace detail
    {
        [[gnu::always_inline]] inline uint64_t
        load64(unsigned char const *const p) noexcept
        {
            uint64_t v;
            std::memcpy(&v, p, 8);
            return v;
        }

        [[gnu::always_inline]] inline uint64_t
        load32(unsigned char const *const p) noexcept
        {
            uint32_t v;
            std::memcpy(&v, p, 4);
            return v;
        }

        // Fold a 128-bit product to 64 bits, mixing the halves rather than
        // dropping one so that neither input word cancels the other.
        [[gnu::always_inline]] inline uint64_t
        mum(uint64_t const a, uint64_t const b) noexcept
        {
            unsigned __int128 const r = static_cast<unsigned __int128>(a) * b;
            return static_cast<uint64_t>(r) ^ static_cast<uint64_t>(r >> 64);
        }
    }

    // The four words that key every map hash of one block. Built from the
    // block hash before any table is populated; changing it afterwards would
    // strand every existing entry. The default is the all-zero placeholder
    // that map move constructors need; it is not a seed, and State rejects
    // it.
    struct KeySeed
    {
        uint64_t k[4]{};

        static KeySeed from_block_hash(bytes32_t const &hash) noexcept
        {
            KeySeed seed;
            for (unsigned i = 0; i < 4; ++i) {
                seed.k[i] = detail::load64(hash.bytes + 8 * i);
            }
            // Odd, so the 4-byte tail of an address keeps every tail
            // distinct for a fixed 16-byte prefix. Also what marks a seed
            // as derived rather than defaulted.
            seed.k[3] |= 1;
            return seed;
        }

        [[nodiscard]] bool seeded() const noexcept
        {
            return (k[3] & 1) != 0;
        }

        bool operator==(KeySeed const &) const = default;
    };

    [[gnu::always_inline]] inline uint64_t
    hash_address(Address const &x, KeySeed const &s) noexcept
    {
        using namespace detail;
        return mum(load64(x.bytes) ^ s.k[0], load64(x.bytes + 8) ^ s.k[1]) +
               (load32(x.bytes + 16) ^ s.k[2]) * s.k[3];
    }

    [[gnu::always_inline]] inline uint64_t
    hash_bytes32(bytes32_t const &x, KeySeed const &s) noexcept
    {
        using namespace detail;
        return mum(load64(x.bytes) ^ s.k[0], load64(x.bytes + 8) ^ s.k[1]) ^
               mum(load64(x.bytes + 16) ^ s.k[2],
                   load64(x.bytes + 24) ^ s.k[3]);
    }

    // Hashers for ankerl maps. They carry the seed, so a table is
    // constructed with one: `Map{bucket_count, AddressHash{seed}}`. The
    // default constructor exists for the map's move operations only.
    struct AddressHash
    {
        using is_avalanching = void;

        KeySeed seed{};

        AddressHash() = default;

        explicit AddressHash(KeySeed const &s) noexcept
            : seed{s}
        {
        }

        [[gnu::always_inline]] inline uint64_t
        operator()(Address const &x) const noexcept
        {
            return hash_address(x, seed);
        }
    };

    struct Bytes32Hash
    {
        using is_avalanching = void;

        KeySeed seed{};

        Bytes32Hash() = default;

        explicit Bytes32Hash(KeySeed const &s) noexcept
            : seed{s}
        {
        }

        [[gnu::always_inline]] inline uint64_t
        operator()(bytes32_t const &x) const noexcept
        {
            return hash_bytes32(x, seed);
        }
    };
}

MONAD_NAMESPACE_END
