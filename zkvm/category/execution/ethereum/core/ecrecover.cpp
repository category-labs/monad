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

// zkVM replacement for category/execution/ethereum/core/ecrecover.cpp.
// Routes transaction-signature recovery through the zkvm_secp256k1_ecrecover
// accelerator instead of libsecp256k1, eliminating both the secp256k1_*
// link surface and the thread_local context (which would otherwise pull in
// __cxa_thread_atexit / __tls_get_addr).

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/endian.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <core/zkvm_accelerators.h>

#include <cstdint>
#include <cstring>
#include <optional>

MONAD_NAMESPACE_BEGIN

std::optional<Address>
ecrecover(SignatureAndChain const &sc, byte_string_view const encoding)
{
    if (sc.y_parity > 1) {
        return std::nullopt;
    }

    if (sc.has_upper_s()) {
        return std::nullopt;
    }

    auto const encoding_hash = keccak256(encoding);

    zkvm_secp256k1_signature signature;
    store_be(signature.data, sc.r);
    store_be(signature.data + sizeof(sc.r), sc.s);

    auto const *msg_hash =
        reinterpret_cast<zkvm_secp256k1_hash const *>(encoding_hash.bytes);

    zkvm_secp256k1_pubkey pubkey;
    if (zkvm_secp256k1_ecrecover(msg_hash, &signature, sc.y_parity, &pubkey) !=
        ZKVM_EOK) {
        return std::nullopt;
    }

    zkvm_bytes_32 key_hash;
    if (zkvm_keccak256(pubkey.data, sizeof(pubkey.data), &key_hash) !=
        ZKVM_EOK) {
        return std::nullopt;
    }

    Address result;
    std::memcpy(result.bytes, key_hash.data + 12, sizeof(result.bytes));
    return result;
}

MONAD_NAMESPACE_END
