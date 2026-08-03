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
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <silkpre_vendor/ecdsa.h>

#include <secp256k1.h>

#include <cstdint>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

std::optional<Address>
recover_address(Secp256k1Signature const &sig, byte_string_view const encoding)
{
    if (sig.y_parity > 1) {
        return std::nullopt;
    }

    if (sig.has_upper_s()) {
        return std::nullopt;
    }

    auto const encoding_hash = keccak256(encoding);

    uint8_t signature[sizeof(sig.r) * 2];
    store_be(signature, sig.r);
    store_be(signature + sizeof(sig.r), sig.s);

    thread_local std::
        unique_ptr<secp256k1_context, void (*)(secp256k1_context *)> const
            context(
                secp256k1_context_create(MONAD_SECP256K1_CONTEXT_FLAGS),
                &secp256k1_context_destroy);

    Address result;

    if (!monad_recover_address(
            result.bytes,
            encoding_hash.bytes,
            signature,
            sig.y_parity,
            context.get())) {
        return std::nullopt;
    }

    return result;
}

MONAD_NAMESPACE_END
