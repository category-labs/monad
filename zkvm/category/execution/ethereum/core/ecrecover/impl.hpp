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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/crypto/keccak.h>

#include <c-interface-accelerators/zkvm_accelerators.h>

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>

MONAD_NAMESPACE_BEGIN

// Must match the definitions in the host
// category/execution/ethereum/core/ecrecover/impl.hpp.
struct RecoverAddressInput
{
    uint8_t msg[32]; ///< message digest
    uint8_t sig[64]; ///< r || s, each 32 bytes big-endian
    uint8_t recid; ///< recovery id (y parity)
};

struct RecoverAddressOutput
{
    uint8_t address[20];
    bool ok;
};

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

    // Hash the recovered public key; its hash's last 20 bytes form the address.
    uint8_t key_hash[KECCAK256_SIZE];
    monad_keccak256(pubkey.data, 64, key_hash);

    std::memcpy(out.data(), key_hash + 12, out.size());

    return true;
}

// The ecrecover accelerator takes one signature per call, so a batch is a loop.
inline void recover_addresses(
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
