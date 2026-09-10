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

#include <optional>

MONAD_NAMESPACE_BEGIN

/// Recovers the Ethereum address that signed `encoding` with the given ECDSA
/// signature. Rejects malformed signatures up-front (y_parity > 1, malleable
/// s); returns nullopt if ECDSA recovery fails.
inline std::optional<Address>
recover_address(Secp256k1Signature const &sig, byte_string_view const encoding)
{
    if (!sig.is_valid()) {
        return std::nullopt;
    }

    auto const encoding_hash = keccak256(encoding);

    uint8_t signature[sizeof(sig.r) * 2];
    store_be(signature, sig.r);
    store_be(signature + sizeof(sig.r), sig.s);

    Address result;

    if (!recover_address(
            result.bytes, encoding_hash.bytes, signature, sig.y_parity)) {
        return std::nullopt;
    }

    return result;
}

MONAD_NAMESPACE_END
