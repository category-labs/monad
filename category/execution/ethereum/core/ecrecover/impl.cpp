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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/crypto/silkpre_vendor/ecdsa.h>
#include <category/execution/ethereum/core/ecrecover/impl.hpp>
#include <category/execution/ethereum/core/ecrecover/types.hpp>

#include <secp256k1.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>

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

    return monad_recover_address(
        out.data(), msg.data(), sig.data(), recid, context.get());
}

// Element-at-a-time reference implementation. A vectorized implementation
// replaces this function and must agree with recover_address on every input.
void recover_addresses(
    std::span<RecoverAddressInput const> const in,
    std::span<RecoverAddressOutput> const out)
{
    MONAD_ASSERT(in.size() == out.size());
    for (size_t i = 0; i < in.size(); ++i) {
        out[i].ok =
            recover_address(out[i].address, in[i].msg, in[i].sig, in[i].recid);
    }
}

MONAD_NAMESPACE_END
