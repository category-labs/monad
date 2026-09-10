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

#include <category/core/config.hpp>

#include <c-interface-accelerators/zkvm_accelerators.h>

#include <cstdint>
#include <cstring>
#include <span>

MONAD_NAMESPACE_BEGIN

[[gnu::always_inline]] inline bool recover_address(
    std::span<uint8_t, 20> const out, std::span<uint8_t const, 32> const msg,
    std::span<uint8_t const, 64> const sig, uint8_t const recid)
{
    auto const *msg_hash =
        reinterpret_cast<zkvm_secp256k1_hash const *>(msg.data());

    auto const *signature =
        reinterpret_cast<zkvm_secp256k1_signature const *>(sig.data());

    zkvm_secp256k1_pubkey pubkey;

    if (zkvm_secp256k1_ecrecover(msg_hash, signature, recid, &pubkey) !=
        ZKVM_EOK) {
        return false;
    }

    zkvm_bytes_32 key_hash;
    if (zkvm_keccak256(pubkey.data, 64, &key_hash) != ZKVM_EOK) {
        return false;
    }

    std::memcpy(out.data(), key_hash.data + 12, out.size());

    return true;
}

MONAD_NAMESPACE_END
