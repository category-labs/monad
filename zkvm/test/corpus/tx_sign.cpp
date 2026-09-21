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

#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>

#include <secp256k1.h>
#include <secp256k1_recovery.h>

#include <cstddef>
#include <cstring>
#include <memory>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using SecpContext =
    std::unique_ptr<secp256k1_context, void (*)(secp256k1_context *)>;

/// SIGN capability, which the two contexts already in the tree do not have:
/// monad::staking::get_secp_context() is VERIFY-only, and the one that can
/// sign is file-local to the staking input generator.
secp256k1_context const *signing_context()
{
    static SecpContext const ctx(
        secp256k1_context_create(
            SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
        &secp256k1_context_destroy);
    return ctx.get();
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    Address address_of(bytes32_t const &secret)
    {
        secp256k1_pubkey pubkey;
        MONAD_ASSERT(
            secp256k1_ec_pubkey_create(
                signing_context(), &pubkey, secret.bytes) == 1);

        unsigned char ser[65];
        std::size_t len = sizeof(ser);
        MONAD_ASSERT(
            secp256k1_ec_pubkey_serialize(
                signing_context(),
                ser,
                &len,
                &pubkey,
                SECP256K1_EC_UNCOMPRESSED) == 1);
        MONAD_ASSERT(len == sizeof(ser) && ser[0] == 0x04);

        // The tag is not hashed: the address is keccak of the 64 coordinate
        // bytes alone.
        auto const hash = keccak256(byte_string_view{ser + 1, 64});
        Address addr;
        std::memcpy(addr.bytes, hash.bytes + 12, sizeof(addr.bytes));
        return addr;
    }

    void sign_transaction(Transaction &tx, bytes32_t const &secret)
    {
        auto const preimage = rlp::encode_transaction_for_signing(tx);
        auto const digest = keccak256(preimage);

        secp256k1_ecdsa_recoverable_signature sig;
        MONAD_ASSERT(
            secp256k1_ecdsa_sign_recoverable(
                signing_context(),
                &sig,
                digest.bytes,
                secret.bytes,
                nullptr, // default RFC6979 nonce: deterministic, so a corpus
                nullptr) // regenerated from the same keys is byte-identical
            == 1);

        unsigned char compact[64];
        int recid = -1;
        MONAD_ASSERT(
            secp256k1_ecdsa_recoverable_signature_serialize_compact(
                signing_context(), compact, &recid, &sig) == 1);
        MONAD_ASSERT(recid == 0 || recid == 1);

        unsigned char r[32];
        unsigned char s[32];
        std::memcpy(r, compact, 32);
        std::memcpy(s, compact + 32, 32);
        tx.sc.signature.r = load_be<uint256_t>(r);
        tx.sc.signature.s = load_be<uint256_t>(s);
        tx.sc.signature.y_parity = static_cast<uint8_t>(recid);

        // libsecp256k1 normalizes s into the lower half, and recover_address
        // rejects anything that is not -- so a violation here would be a
        // library change, not a caller mistake, and it would surface as every
        // sender recovering to nullopt. Cheaper to catch it at the source.
        MONAD_ASSERT(tx.sc.signature.is_valid());
        MONAD_ASSERT(!tx.sc.signature.has_upper_s());
    }
}

MONAD_NAMESPACE_END
