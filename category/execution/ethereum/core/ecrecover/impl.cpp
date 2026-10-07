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

#include <category/crypto/silkpre_vendor/ecdsa.h>
#include <category/execution/ethereum/core/ecrecover/impl.hpp>
#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
    #include <category/execution/ethereum/core/signature_hash.hpp>

    #include <secp256k1_recovery.h>
#endif

#include <secp256k1.h>

#include <cstddef>
#include <memory>

MONAD_NAMESPACE_BEGIN

bool recover_address(
    std::span<uint8_t, 20> const out, std::span<uint8_t const, 32> const msg,
    std::span<uint8_t const, 64> const sig, uint8_t const recid)
{

    thread_local std::
        unique_ptr<secp256k1_context, void (*)(secp256k1_context *)> const
            context(
                secp256k1_context_create(MONAD_SECP256K1_CONTEXT_FLAGS),
                &secp256k1_context_destroy);

#ifdef MONAD_L2_SIGNATURE_HASH_POSEIDON2
    // silkpre's monad_recover_address hashes the key with keccak256, and this
    // chain derives addresses with its own hash: recover the key here and
    // derive the address the guest derives.
    secp256k1_ecdsa_recoverable_signature parsed;
    if (!secp256k1_ecdsa_recoverable_signature_parse_compact(
            context.get(), &parsed, sig.data(), recid)) {
        return false;
    }
    secp256k1_pubkey key;
    if (!secp256k1_ecdsa_recover(context.get(), &key, &parsed, msg.data())) {
        return false;
    }
    uint8_t serialized[65];
    size_t len = sizeof(serialized);
    secp256k1_ec_pubkey_serialize(
        context.get(), serialized, &len, &key, SECP256K1_EC_UNCOMPRESSED);
    pubkey_address(std::span<uint8_t const, 64>{serialized + 1, 64}, out);
    return true;
#else
    return monad_recover_address(
        out.data(), msg.data(), sig.data(), recid, context.get());
#endif
}

MONAD_NAMESPACE_END
