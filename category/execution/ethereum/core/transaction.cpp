// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>

#include <silkpre/ecdsa.h>

#include <ethash/hash_types.hpp>

#include <intx/intx.hpp>

#include <secp256k1.h>

#include <cstdint>
#include <memory>
#include <optional>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

/// Recover an Ethereum address from an ECDSA signature.
///
/// @param sc            The signature and chain information.
/// @param encoding      The RLP-encoded payload that was signed.
/// @param allow_high_s  When true, accept signatures whose `s` value lies in
///                      the upper half of the secp256k1 curve order; when
///                      false, reject such "high-s" signatures.
///
/// This distinction exists because:
/// - For transaction sender recovery (`recover_sender`), we must be able to
///   recover senders of legacy pre-EIP-2 transactions that may use high-s
///   signatures. Therefore `allow_high_s` is set to true.
/// - For EIP-7702 authorization recovery (`recover_authority`), signatures
///   are created under the post-EIP-2 non-malleability rules and MUST use a
///   low-s value, so `allow_high_s` is set to false to enforce that
///   requirement.
std::optional<Address> ecrecover(
    SignatureAndChain const &sc, byte_string_view encoding,
    bool const allow_high_s)
{
    if (sc.y_parity > 1) {
        return std::nullopt;
    }

    if (!allow_high_s && sc.has_upper_s()) {
        return std::nullopt;
    }

    auto const encoding_hash = keccak256(encoding);

    uint8_t signature[sizeof(sc.r) * 2];
    intx::be::unsafe::store(signature, sc.r);
    intx::be::unsafe::store(signature + sizeof(sc.r), sc.s);

    thread_local std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        context(
            secp256k1_context_create(SILKPRE_SECP256K1_CONTEXT_FLAGS),
            &secp256k1_context_destroy);

    Address result;

    if (!silkpre_recover_address(
            result.bytes,
            encoding_hash.bytes,
            signature,
            sc.y_parity,
            context.get())) {
        return std::nullopt;
    }

    return result;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::optional<Address> recover_authority(AuthorizationEntry const &auth_entry)
{
    byte_string const auth_encoding =
        rlp::encode_authorization_entry_for_signing(auth_entry);
    return ecrecover(auth_entry.sc, auth_encoding, false);
}

std::optional<Address> recover_sender(Transaction const &tx)
{
    TRACE_TXN_EVENT(StartSenderRecovery);
    byte_string const tx_encoding = rlp::encode_transaction_for_signing(tx);
    return ecrecover(tx.sc, tx_encoding, true);
}

MONAD_NAMESPACE_END
