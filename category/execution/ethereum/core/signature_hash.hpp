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

// The two hashes this chain's signatures are bound with: the digest an ECDSA
// signature signs -- of a transaction's signing encoding, or an
// authorization's -- and the hash that turns the public key a signature
// recovers into an address. Ethereum's keccak256 for both, except in an L2
// built with MONAD_ZKVM_L2_SIGNATURE_HASH=poseidon2, where both are
// monad_poseidon2_256 over a label of their own and the bytes keccak would
// have hashed: ZisK's Poseidon2 precompile in the guest, the same permutation
// in software on the host. The curve stays secp256k1 and the signature ECDSA,
// whose recovery the guest already runs on ZisK's curve precompiles.
//
// The labels keep the two uses, and the tries' (category/core/trie_hash.hpp),
// separate oracles: a digest never doubles as an address or a node reference.
// Each fits the sponge's first 88-byte block beside what it prefixes, so an
// address is one permutation, and so is the digest of a signing encoding of up
// to 69 bytes.
//
// The address hash applies wherever this chain turns a key into an address: a
// transaction's sender, an authorization's authority, and the ECRECOVER
// precompile, so that a contract checking a signature finds the signer's
// account. CREATE and CREATE2 addresses hash no key and stay keccak256.

#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/crypto/hash256.h>
#include <category/crypto/keccak.h>
#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
    #include <category/core/poseidon2.hpp>
#endif

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <string_view>

MONAD_NAMESPACE_BEGIN

#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
inline constexpr std::string_view SIGNING_DIGEST_LABEL = "monad-l2/tx-sig/v1";
inline constexpr std::string_view ADDRESS_LABEL = "monad-l2/address/v1";
#endif

/// The 32 bytes an ECDSA signature over `encoding` signs.
inline monad_hash256 signing_digest(byte_string_view const encoding)
{
#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
    byte_string buf;
    buf.reserve(SIGNING_DIGEST_LABEL.size() + encoding.size());
    buf.append(
        reinterpret_cast<unsigned char const *>(SIGNING_DIGEST_LABEL.data()),
        SIGNING_DIGEST_LABEL.size());
    buf.append(encoding);
    monad_hash256 digest;
    monad_poseidon2_256(buf.data(), buf.size(), digest.bytes);
    return digest;
#else
    return keccak256(encoding);
#endif
}

/// The address of the uncompressed public key x || y (big-endian, no tag).
inline void pubkey_address(
    std::span<uint8_t const, 64> const pubkey, std::span<uint8_t, 20> const out)
{
    uint8_t hash[KECCAK256_SIZE];
#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
    unsigned char buf[ADDRESS_LABEL.size() + 64];
    std::memcpy(buf, ADDRESS_LABEL.data(), ADDRESS_LABEL.size());
    std::memcpy(buf + ADDRESS_LABEL.size(), pubkey.data(), 64);
    monad_poseidon2_256(buf, sizeof(buf), hash);
#else
    monad_keccak256(pubkey.data(), 64, hash);
#endif
    std::memcpy(out.data(), hash + 12, out.size());
}

MONAD_NAMESPACE_END
