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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/endian.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
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

    uint8_t signature[sizeof(sc.r) * 2];
    store_be(signature, sc.r);
    store_be(signature + sizeof(sc.r), sc.s);

    thread_local std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        context(
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);

    secp256k1_ecdsa_recoverable_signature sig;
    if (!secp256k1_ecdsa_recoverable_signature_parse_compact(
            context.get(), &sig, signature, sc.y_parity)) {
        return std::nullopt;
    }

    secp256k1_pubkey pub_key;
    if (!secp256k1_ecdsa_recover(
            context.get(), &pub_key, &sig, encoding_hash.bytes)) {
        return std::nullopt;
    }

    uint8_t public_key[65];
    size_t key_len = sizeof(public_key);
    secp256k1_ec_pubkey_serialize(
        context.get(),
        public_key,
        &key_len,
        &pub_key,
        SECP256K1_EC_UNCOMPRESSED);

    // Uncompressed pubkey is 0x04 || X(32) || Y(32). keccak256 of X||Y
    // and the bottom 20 bytes are the Ethereum address.
    if (public_key[0] != 4u) {
        return std::nullopt;
    }

    auto const key_hash =
        keccak256(byte_string_view{public_key + 1, sizeof(public_key) - 1});
    Address result;
    std::memcpy(result.bytes, key_hash.bytes + 12, sizeof(result.bytes));
    return result;
}

MONAD_NAMESPACE_END
