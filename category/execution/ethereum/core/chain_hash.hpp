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

// The hashes this chain defines beyond its tries (category/core/trie_hash.hpp)
// and its signatures (signature_hash.hpp): a block's hash, of its header's RLP,
// and the hash a logs bloom takes its three bits from. Ethereum's keccak256 for
// both, except in an L2 built with MONAD_ZKVM_L2_HASH=poseidon2, where both are
// monad_poseidon2_256 over a label of their own and the bytes keccak would have
// hashed: ZisK's Poseidon2 precompile in the guest, the same permutation in
// software on the host.
//
// The block hash is what a header's parent_hash names, what BLOCKHASH returns
// and what the guest publishes; the L1 hub only ever compares two of them, so
// it takes either. The bloom is in every receipt, so the receipts root commits
// to it. Neither is what the EVM computes for a contract: that stays keccak256.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/crypto/hash256.h>
#ifdef MONAD_L2_HASH_POSEIDON2
    #include <category/core/poseidon2.hpp>
#endif

#include <string_view>

MONAD_NAMESPACE_BEGIN

#ifdef MONAD_L2_HASH_POSEIDON2
inline constexpr std::string_view HEADER_HASH_LABEL = "monad-l2/header/v1";
inline constexpr std::string_view BLOOM_HASH_LABEL = "monad-l2/bloom/v1";

/// The Poseidon2 sponge over `label` then `bytes`.
inline monad_hash256
labelled_poseidon2(std::string_view const label, byte_string_view const bytes)
{
    byte_string buf;
    buf.reserve(label.size() + bytes.size());
    buf.append(
        reinterpret_cast<unsigned char const *>(label.data()), label.size());
    buf.append(bytes);
    monad_hash256 hash;
    monad_poseidon2_256(buf.data(), buf.size(), hash.bytes);
    return hash;
}
#endif

/// A block's hash: of its header's RLP encoding.
inline monad_hash256 header_hash(byte_string_view const header_rlp)
{
#ifdef MONAD_L2_HASH_POSEIDON2
    return labelled_poseidon2(HEADER_HASH_LABEL, header_rlp);
#else
    return keccak256(header_rlp);
#endif
}

/// The hash a logs bloom sets three bits from: of a log's address or of one of
/// its topics.
inline monad_hash256 bloom_hash(byte_string_view const entry)
{
#ifdef MONAD_L2_HASH_POSEIDON2
    return labelled_poseidon2(BLOOM_HASH_LABEL, entry);
#else
    return keccak256(entry);
#endif
}

MONAD_NAMESPACE_END
