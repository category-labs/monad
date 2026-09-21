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

// Where the compiled deployment constants become the cipher's context. See
// l2_config.hpp for why none of them has a default.

#include <zkvm/guest/l2_config.hpp>

#include <category/execution/ethereum/core/block.hpp>
#include <zkvm/guest/l2_cipher.hpp>

#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>

#include <cstring>
#include <span>
#include <string_view>

MONAD_NAMESPACE_BEGIN

bytes32_t l2_state_salt(
    std::span<unsigned char const, 32> const salt_secret,
    std::uint64_t const block_number)
{
    // A label, the secret, then the number. The label keeps this hash from
    // colliding with any other use of the same secret, and the number is what
    // makes the blinder per-block.
    static constexpr std::string_view LABEL = "monad-l2/state-salt/v1";

    byte_string buf;
    buf.reserve(LABEL.size() + 32 + 8);
    buf.append(
        reinterpret_cast<unsigned char const *>(LABEL.data()), LABEL.size());
    buf.append(salt_secret.data(), salt_secret.size());
    // Big-endian, like every other multi-byte quantity that reaches the wire
    // here.
    for (unsigned i = 0; i < 8; ++i) {
        buf.push_back(static_cast<unsigned char>(block_number >> (56 - 8 * i)));
    }
    return to_bytes(keccak256(buf));
}

L2Cipher::Context l2_cipher_context(BlockHeader const &header)
{
    L2Cipher::Context ctx{};
    ctx.version = L2_CIPHER_VERSION;
    ctx.chain_id = L2_CHAIN_ID;
    ctx.contract = L2_NAMESPACE_SPOKE;
    ctx.namespace_id = L2_NAMESPACE_ID;
    ctx.epoch = header.number / L2_EPOCH_BLOCKS;
    ctx.operator_pk[0] = L2_OPERATOR_PK_ODD ? 0x03 : 0x02;
    std::memcpy(
        ctx.operator_pk + 1,
        L2_OPERATOR_PK_X.bytes,
        sizeof(L2_OPERATOR_PK_X.bytes));
    // Once a block. Every sponge then reads only this, which is what keeps the
    // constants off the per-transaction path.
    ctx.constants_digest = l2_constants_digest(ctx);
    return ctx;
}

MONAD_NAMESPACE_END
