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
#ifdef MONAD_L2_HASH_POSEIDON2
    #include <category/core/poseidon2.hpp>
#endif

#include <cstring>
#include <span>
#include <string_view>

MONAD_NAMESPACE_BEGIN

bytes32_t l2_state_salt(
    std::span<unsigned char const, 32> const salt_secret,
    std::uint64_t const block_number)
{
    // Bind the label, secret, domain and height so shared seeds do not reuse
    // blinders across domains or blocks. The versioned label fixes this
    // encoding.
    static constexpr std::string_view LABEL = "monad-l2/state-salt/v2";

    byte_string buf;
    buf.reserve(LABEL.size() + 32 + 8 + 8);
    buf.append(
        reinterpret_cast<unsigned char const *>(LABEL.data()), LABEL.size());
    buf.append(salt_secret.data(), salt_secret.size());
    // Big-endian, like every other multi-byte quantity that reaches the wire
    // here.
    for (unsigned i = 0; i < 8; ++i) {
        buf.push_back(static_cast<unsigned char>(L2_CHAIN_ID >> (56 - 8 * i)));
    }
    for (unsigned i = 0; i < 8; ++i) {
        buf.push_back(static_cast<unsigned char>(block_number >> (56 - 8 * i)));
    }
#ifdef MONAD_L2_HASH_POSEIDON2
    bytes32_t salt;
    monad_poseidon2_256(buf.data(), buf.size(), salt.bytes);
    return salt;
#else
    return to_bytes(keccak256(buf));
#endif
}

bytes32_t l2_state_commitment(
    std::span<unsigned char const, 32> const salt_secret,
    std::uint64_t const block_number, bytes32_t const &state_root)
{
    // Use the chain hash: the client reopens this commitment, while L1 only
    // stores and compares it. See zkvm/DECISIONS.md.
    static constexpr std::string_view LABEL = "monad-l2/state-commitment/v1";

    bytes32_t const salt = l2_state_salt(salt_secret, block_number);
    byte_string buf;
    buf.reserve(LABEL.size() + 32 + 32);
    buf.append(
        reinterpret_cast<unsigned char const *>(LABEL.data()), LABEL.size());
    buf.append(salt.bytes, sizeof(salt.bytes));
    buf.append(state_root.bytes, sizeof(state_root.bytes));
#ifdef MONAD_L2_HASH_POSEIDON2
    bytes32_t commitment;
    monad_poseidon2_256(buf.data(), buf.size(), commitment.bytes);
    return commitment;
#else
    return to_bytes(keccak256(buf));
#endif
}

bytes32_t
l2_salt_commitment(std::span<unsigned char const, 32> const salt_secret)
{
#ifdef MONAD_L2_HASH_POSEIDON2
    // A label of its own, so the commitment is no other use's hash of the
    // secret -- the state salt's least of all.
    static constexpr std::string_view LABEL = "monad-l2/salt-commitment/v1";
    byte_string buf;
    buf.reserve(LABEL.size() + salt_secret.size());
    buf.append(
        reinterpret_cast<unsigned char const *>(LABEL.data()), LABEL.size());
    buf.append(salt_secret.data(), salt_secret.size());
    bytes32_t commitment;
    monad_poseidon2_256(buf.data(), buf.size(), commitment.bytes);
    return commitment;
#else
    return to_bytes(
        keccak256(byte_string_view{salt_secret.data(), salt_secret.size()}));
#endif
}

#if defined(MONAD_L2_CIPHER_PLAINTEXT)
L2Cipher::Context l2_cipher_context(BlockHeader const &)
{
    // The plaintext suite takes nothing from the block or the deployment.
    return L2Cipher::Context{};
}
#else
// Nothing of the block reaches the context any more: with the epoch gone, every
// field is a compiled constant. The parameter stays so that a suite which does
// want the header can have it without moving every call site.
L2Cipher::Context l2_cipher_context(BlockHeader const &)
{
    L2Cipher::Context ctx{};
    ctx.version = L2_CIPHER_VERSION;
    ctx.chain_id = L2_CHAIN_ID;
    ctx.contract = L2_DOMAIN_SPOKE;
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
#endif

MONAD_NAMESPACE_END
