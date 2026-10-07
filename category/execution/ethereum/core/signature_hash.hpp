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

// Transaction/authorization signing digests and public-key address hashes:
// keccak256 by default, domain-separated monad_poseidon2_256 with
// MONAD_ZKVM_L2_SIGNATURE_HASH=poseidon2. ECDSA stays on secp256k1.
//
// Distinct labels separate signatures, addresses and trie nodes. The 88-byte
// rate fits an address or a signing encoding of up to 69 bytes in one block.
//
// Address hashing applies to senders, authorities and ECRECOVER so contracts
// recover the same accounts as transaction validation. CREATE/CREATE2 remain
// Keccak-based because they do not hash public keys.

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
