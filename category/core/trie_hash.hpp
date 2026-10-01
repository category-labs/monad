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

// The hash the Merkle-Patricia tries are built with: the reference a node gets
// in its parent, the root a trie is committed to, and the path a secure trie
// keeps an account, a slot or a storage page under. Ethereum's keccak256,
// except in an L2 built with MONAD_ZKVM_L2_TRIE_HASH=poseidon2, where it is
// monad_poseidon2_256 -- ZisK's Poseidon2 precompile in the guest, the same
// permutation in software on the host, so the witness generator and the guest
// compute the same nodes by construction. Every trie is built with it: the
// state and storage tries, and the ordered tries behind a header's
// transactions, receipts and withdrawals roots.
//
// Only the tries switch. What Ethereum, a wallet or the L1 computes stays
// keccak256 whatever this says: the KECCAK256 opcode, code hashes, contract
// addresses, transaction hashes and signatures, the logs bloom, the block hash
// and the namespace anchor. The empty trie keeps its sentinel, NULL_ROOT, on
// both sides: no path hashes an empty node to compare against it.

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
