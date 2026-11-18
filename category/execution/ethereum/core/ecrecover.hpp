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

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/ecrecover/impl.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <cstring>
#include <optional>

MONAD_NAMESPACE_BEGIN

/// Prepares the recovery of the Ethereum address that signed `encoding` with
/// the given ECDSA signature, for recover_address or a recover_addresses
/// batch. Returns nullopt for a malformed signature (y_parity > 1, r or s out
/// of range, malleable s), which has no signer.
inline std::optional<RecoverAddressInput> make_recover_address_input(
    Secp256k1Signature const &sig, byte_string_view const encoding)
{
    static_assert(sizeof(RecoverAddressInput::sig) == 2 * sizeof(sig.r));

    if (!sig.is_valid()) {
        return std::nullopt;
    }

    RecoverAddressInput input;
    auto const encoding_hash = keccak256(encoding);
    std::memcpy(input.msg, encoding_hash.bytes, sizeof(input.msg));
    store_be(input.sig, sig.r);
    store_be(input.sig + sizeof(sig.r), sig.s);
    input.recid = sig.y_parity;
    return input;
}

/// Converts one recover_addresses result to an address; nullopt if ECDSA
/// recovery failed.
inline std::optional<Address> to_address(RecoverAddressOutput const &output)
{
    if (!output.ok) {
        return std::nullopt;
    }
    Address result;
    static_assert(sizeof(result.bytes) == sizeof(output.address));
    std::memcpy(result.bytes, output.address, sizeof(result.bytes));
    return result;
}

/// Recovers the Ethereum address that signed `encoding` with the given ECDSA
/// signature. Rejects malformed signatures up-front (y_parity > 1, malleable
/// s); returns nullopt if ECDSA recovery fails.
inline std::optional<Address>
recover_address(Secp256k1Signature const &sig, byte_string_view const encoding)
{
    auto const input = make_recover_address_input(sig, encoding);
    if (!input.has_value()) {
        return std::nullopt;
    }

    Address result;

    if (!recover_address(result.bytes, input->msg, input->sig, input->recid)) {
        return std::nullopt;
    }

    return result;
}

MONAD_NAMESPACE_END
