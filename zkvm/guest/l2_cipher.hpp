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

// The L2's transaction encryption: ECDH on secp256k1, Poseidon2 masks over
// Goldilocks, and a Poseidon2 tag over the ciphertext -- Encrypt-then-MAC.
//
//   R = rG,  P = r*pk        (sender)          P = sk*R      (guest)
//   A = (version, chain, contract, namespace, epoch, pk | R, N, len)
//   K = H_KDF(P, A; 4)
//   Z = H_STREAM(K, A; l)    C_i = M_i + Z_i (mod p)
//   T = H_AUTH(K, A, C; 4)
//
// The three H_d are separated uses of one SAFE sponge (l2_sponge.hpp), so the
// argument can treat them as independent oracles. Neither K, nor P, nor r is
// ever published.
//
// A is written with a bar above because its two halves reach the sponge by
// different routes. Everything left of the bar is constant across the block,
// so it is hashed once and handed to each sponge as its SAFE domain context --
// where application binding belongs, and where it binds just as tightly, the
// tag determining every lane the sponge will produce. Only R, N and the length
// are absorbed per transaction. That is not a reformulation for its own sake:
// it takes thirteen elements off the per-transaction path in all three
// domains: 36 absorptions a transaction, for one extra permutation a block.
//
// Which is also why the halves are not simply reordered so a pre-absorbed
// prefix could be cloned. SAFE puts the lengths in the I/O pattern and the
// pattern into the tag, so H_STREAM and H_AUTH have a different initial state
// for every message length and have no prefix to share; only H_KDF's pattern
// is length-independent. Moving the constants into the tag works for all
// three.
//
// THIS IS NOT AN AUDITED CONSTRUCTION. The pieces are standard -- DH, a sponge
// used as a PRF and as a MAC, encrypt-then-MAC -- but this combination is not,
// and the target of about 128 classical bits rests on DH and on Poseidon2
// behaving as the argument assumes. An independent audit is a precondition of
// deployment, not of the prototype.
//
// Verification order is normative and the code is shaped so it cannot be
// inverted by accident: the tag is checked in full BEFORE a single mask is
// applied. Every failure is a DETERMINISTIC REJECTION of one entry -- the
// queue entry is consumed, no state changes, no receipt is produced, and the
// block stays valid. Nothing here halts the proof.

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <zkvm/guest/l2_ecdh.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

/// The context the scheme calls A, split by how often it changes.
///
/// Its block-constant half -- version, chain id, contract, namespace, epoch and
/// the operator key -- does NOT go into the sponge's rate. It is hashed once a
/// block into `constants_digest` and handed to the sponge as its domain
/// context, which is where SAFE puts application binding. That binds it just as
/// tightly, since the tag determines every lane the sponge produces, and it
/// keeps thirteen elements off the per-transaction path in all three domains:
/// 36 absorptions a transaction, roughly 14,300 ZisK cells, against one
/// extra Poseidon2 permutation a block to compute the digest.
///
/// What remains absorbed per transaction is R, N and the message length, which
/// change every time and so had nothing to share.
///
/// Every field here is either a compiled protocol constant or a header field,
/// so none of it is the prover's to choose -- an explicit salt in the witness
/// would be.
struct L2CipherContext
{
    std::uint64_t version;
    std::uint64_t chain_id;
    Address contract;
    std::uint64_t namespace_id;
    std::uint64_t epoch;
    /// The operator's public key, compressed. The guest checks sk*G against
    /// this once per block; without that check the key is the prover's to pick
    /// and the proof says nothing.
    unsigned char operator_pk[33];

    /// The hash of the six fields above, from l2_constants_digest. Populated
    /// once a block; the sponges read only this.
    bytes32_t constants_digest;
};

/// Hashes the block-constant half of A into the 32 bytes the sponge takes as
/// its domain context: the six fields at fixed widths, so the encoding is
/// injective without carrying its own lengths.
bytes32_t l2_constants_digest(L2CipherContext const &ctx);

/// Wire layout of one encrypted transaction, the content of its RLP string and
/// therefore the leaf the transactions root commits to:
///
///   R    33  compressed SEC1 point
///   N    16  nonce
///   len   4  plaintext length, big-endian u32
///   C    8l  ciphertext field elements, little-endian u64 each
///   T    32  tag, four little-endian u64 lanes
///
/// l is ceil(len/7), so a leaf is 85 + 8*ceil(len/7) bytes. Plaintext packs at
/// seven bytes per element and ciphertext elements take eight, because C_i < p
/// does not fit in seven -- an expansion of about one seventh, inherent to
/// adding in the field, and it belongs in the data-availability budget.
inline constexpr std::size_t L2_LEAF_R_OFFSET = 0;
inline constexpr std::size_t L2_LEAF_NONCE_OFFSET = 33;
inline constexpr std::size_t L2_LEAF_LEN_OFFSET = 49;
inline constexpr std::size_t L2_LEAF_C_OFFSET = 53;
inline constexpr std::size_t L2_LEAF_OVERHEAD = 85;

/// The per-transaction half of A once serialized: R, N and the length, at
/// fixed widths so the encoding is injective without a length prefix of its
/// own. The block-constant half is not here -- it reaches the sponge through
/// constants_digest, see L2CipherContext.
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

/// Verifies and decrypts one leaf, resizing `plain` to the declared length.
///
/// False is a deterministic rejection -- a malformed envelope, an R that is not
/// a curve point, an ECDH that lands on the identity, or a tag that does not
/// verify. It is not an error to report: the caller consumes the entry and
/// carries on.
bool l2_decrypt_leaf(
    L2CipherContext const &ctx, L2Scalar const &sk,
    std::span<unsigned char const> leaf, std::vector<unsigned char> &plain);

/// The sender's side, for the witness generator and for tests. `r` is the
/// ephemeral scalar; it and the derived K are not recoverable from the leaf.
/// False when `r` is not a valid scalar or `ctx.operator_pk` is not a point.
///
/// Not part of the suite interface: the guest never encrypts, so the sender's
/// side is not in the proved path and a replacement suite is free to shape it
/// however its senders need.
bool l2_encrypt_leaf(
    L2CipherContext const &ctx, L2Scalar const &r,
    std::span<unsigned char const, 16> nonce,
    std::span<unsigned char const> plain, std::vector<unsigned char> &leaf);

/// This file's scheme as a cipher suite -- the form the proved path consumes it
/// in. Satisfies L2CipherSuite, which is declared in l2_cipher_suite.hpp
/// alongside the build-time selection; the concept is asserted there rather
/// than here so this header stays the scheme and not the seam.
///
/// The members are thin: everything is above, and this exists so that the
/// decoder and ffi.cpp name a suite instead of naming secp256k1.
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
