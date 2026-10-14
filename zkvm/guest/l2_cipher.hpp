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

// L2 Encrypt-then-MAC: secp256k1 ECDH and Poseidon2 over Goldilocks.
//
// R = rG; P = r*pk (sender) = sk*R (guest)
// A = (version, chain, contract, pk | R, N, len)
// K = H_KDF(P, A; 4)
// Z = H_STREAM(K, A; l); C_i = M_i + Z_i (mod p)
// T = H_AUTH(K, A, C; 4)
//
// KDF, STREAM and AUTH use domain-separated SAFE sponges (l2_sponge.hpp). P,
// K and r remain private. Hash block constants once into the SAFE context;
// absorb only R, N and len per transaction. STREAM/AUTH tags depend on
// length, so a shared absorbed prefix cannot replace this context binding.
//
// This construction is unaudited; its roughly 128-bit classical target
// depends on DH and Poseidon2 assumptions. Audit before deployment. Verify
// the full tag before applying masks. Malformed leaves are deterministically
// consumed and skipped, without state changes or receipts.

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <zkvm/guest/l2_ecdh.hpp>
#include <zkvm/guest/l2_sponge.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

/// Context A: hash version, chain id, contract and operator key once into
/// constants_digest, used in SAFE tags. Only R, nonce and message length are
/// absorbed per transaction.
struct L2CipherContext
{
    std::uint64_t version;
    std::uint64_t chain_id;
    Address contract;
    /// The operator's public key, compressed. The guest checks sk*G against
    /// this once per block; without that check the key is the prover's to pick
    /// and the proof says nothing.
    unsigned char operator_pk[33];

    /// The hash of the four fields above, from l2_constants_digest. Populated
    /// once a block; the sponges read only this.
    bytes32_t constants_digest;

    /// Mutable cache of SAFE tags, not a protocol field. Checks its context
    /// before reuse, so a recomputed digest cannot reuse stale tags. Use each
    /// context from only one thread at a time.
    mutable L2SpongeTags sponge_tags;
};

/// Hashes the block-constant half of A into the 32 bytes the sponge takes as
/// its domain context: the six fields at fixed widths, so the encoding is
/// injective without carrying its own lengths.
bytes32_t l2_constants_digest(L2CipherContext const &ctx);

/// Ciphertext wire layout:
/// R: 33-byte compressed SEC1 point
/// N: 16-byte nonce
/// len: 4-byte big-endian plaintext length
/// C: 8*l bytes, canonical little-endian u64 field elements
/// T: 32-byte tag, four little-endian u64 lanes
///
/// l = ceil(len/7); total size = 85 + 8*l. Plaintext packs seven bytes per
/// element; ciphertext requires eight.
inline constexpr std::size_t L2_LEAF_R_OFFSET = 0;
inline constexpr std::size_t L2_LEAF_NONCE_OFFSET = 33;
inline constexpr std::size_t L2_LEAF_LEN_OFFSET = 49;
inline constexpr std::size_t L2_LEAF_C_OFFSET = 53;
inline constexpr std::size_t L2_LEAF_OVERHEAD = 85;

/// Fixed-width per-transaction context: R, nonce and length. Block constants
/// enter through constants_digest.
inline constexpr std::size_t L2_CONTEXT_BYTES = 57; // 33 + 16 + 8
inline constexpr std::size_t L2_CONTEXT_ELEMS = 9; // ceil(57/7)

/// Number of ciphertext elements a plaintext of `len` bytes produces.
constexpr std::size_t l2_elem_count(std::size_t const len) noexcept
{
    return (len + 6) / 7;
}

constexpr std::size_t l2_leaf_size(std::size_t const len) noexcept
{
    return L2_LEAF_OVERHEAD + 8 * l2_elem_count(len);
}

/// True when sk is the operator key this context names. One fixed-base scalar
/// multiplication, called once per block; see the header note on why it is not
/// optional.
bool l2_check_operator_key(L2CipherContext const &ctx, L2Scalar const &sk);

/// Verify/decrypt one leaf and resize plain to its declared length. Malformed
/// envelopes, invalid points, identity ECDH or bad tags return false; the
/// caller consumes and skips the entry.
bool l2_decrypt_leaf(
    L2CipherContext const &ctx, L2Scalar const &sk,
    std::span<unsigned char const> leaf, std::vector<unsigned char> &plain);

/// Sender-side encryption for corpus generation/tests. Reject invalid r or
/// operator_pk. Not part of the guest suite interface; replacement suites may
/// expose different sender APIs.
bool l2_encrypt_leaf(
    L2CipherContext const &ctx, L2Scalar const &r,
    std::span<unsigned char const, 16> nonce,
    std::span<unsigned char const> plain, std::vector<unsigned char> &leaf);

/// L2EcdhPoseidon2 adapts this scheme to L2CipherSuite. The concept check and
/// build-time selection live in l2_cipher_suite.hpp, keeping decoder and
/// witness execution independent of the concrete cipher.
struct L2EcdhPoseidon2
{
    using Context = L2CipherContext;

    /// The operator's secp256k1 scalar. Only bind_secret produces one, so a
    /// value of this type has been checked against its context.
    using Secret = L2Scalar;

    /// Carries the protocol version, so bumping L2_CIPHER_VERSION alone cannot
    /// leave two versions sharing a sponge domain. It reaches every tag.
    static constexpr std::string_view LABEL = "monad-l2/ecdh-poseidon2/v1/";

    /// 32 big-endian bytes, then l2_check_operator_key. Nullopt unless they are
    /// the secret `ctx` names -- see the note on that function.
    static std::optional<Secret>
    bind_secret(Context const &ctx, std::span<unsigned char const, 32> bytes);

    static bool decrypt(
        Context const &ctx, Secret const &secret,
        std::span<unsigned char const> leaf, std::vector<unsigned char> &plain);
};

MONAD_NAMESPACE_END
