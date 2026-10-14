// Copyright (C) 2026 Category Labs, Inc.
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

// Hash for state, storage and ordered Merkle-Patricia tries, including secure
// paths: keccak256 by default, monad_poseidon2_256 with
// MONAD_ZKVM_L2_TRIE_HASH=poseidon2. Host and guest share the sponge.
//
// This option does not change EVM hashing, code/contract addresses,
// signatures, blooms, block hashes or message anchors. Both modes retain
// NULL_ROOT as the empty-trie sentinel; no empty node is hashed.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/crypto/hash256.h>
#include <category/crypto/keccak.h>
#ifdef MONAD_L2_TRIE_HASH_POSEIDON2
    #include <category/core/poseidon2.hpp>
#endif

#include <cstddef>
#include <cstdint>

[[gnu::always_inline]] inline void monad_trie_hash256(
    void const *const in, size_t const len, uint8_t out[KECCAK256_SIZE])
{
#ifdef MONAD_L2_TRIE_HASH_POSEIDON2
    monad_poseidon2_256(in, len, out);
#else
    monad_keccak256(in, len, out);
#endif
}

MONAD_NAMESPACE_BEGIN

inline monad_hash256 trie_hash(byte_string_view const bytes)
{
    monad_hash256 hash;
    monad_trie_hash256(bytes.data(), bytes.size(), hash.bytes);
    return hash;
}

template <size_t N>
inline monad_hash256 trie_hash(unsigned char const (&a)[N])
{
    return trie_hash(to_byte_string_view(a));
}

MONAD_NAMESPACE_END
