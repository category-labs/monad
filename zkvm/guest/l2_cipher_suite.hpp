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

// The seam the L2's encryption is swapped at: what the proved path requires of
// a cipher suite, the concept that checks a candidate provides it, and the
// build-time selection of the one in use.
//
// The point of naming an interface for something with one implementation is
// that the encryption is the part of this design most likely to be replaced --
// it is explicitly not an audited construction -- and a seam is far cheaper to
// put in before there is a second suite than to extract afterwards from the
// three files that would by then name secp256k1 in their signatures.
//
// WHAT IS BEHIND THE SEAM. Everything about how a leaf is built: the wire
// format, the curve or the absence of one, the field, the sponge, the tag, the
// packing density. The two entry points below take bytes and return bytes, so
// none of it reaches decode_block_l2 or ffi.cpp.
//
// WHAT IS NOT, and cannot be moved behind it:
//
//   - The decision rule. A leaf that fails is a DETERMINISTIC REJECTION of one
//     queue entry, never a halt: `decrypt` returns false, the caller consumes
//     the entry, no state changes, no receipt is produced, and the block stays
//     valid. A suite whose failures halt would be a different protocol, not a
//     different cipher.
//
//   - The binding of the secret. `bind_secret` is the only way to obtain a
//     Secret, and it must fail unless the witness's 32 bytes are the secret
//     this context names. That is the load-bearing check of the whole design:
//     the secret is a private witness input, so without it a prover supplies
//     any secret, obtains another set of plaintexts, and proves a valid
//     post-state for a block nobody wrote. It is in the interface rather than
//     left to the caller because a suite cannot be correct without it, and a
//     Secret that exists is one that has been bound.
//
//   - Determinism. Every check must be a function of (leaf, secret, context),
//     so that a rejection is the same rejection for every prover.
//
// NO RUNTIME DISPATCH. The suite is a compile-time alias, so an L2 guest
// contains exactly one and the unselected suites are not linked at all. That
// matches what MONAD_ZKVM_L2 already is -- a mode, not an optimisation -- and
// it keeps the cost of the seam at zero instructions.
//
// COMPARING TWO SUITES therefore means two ELFs and two runs under ziskemu, the
// way the corpus differential already compares the plaintext and L2 arms. What
// that gives is a total, not a breakdown: there is no per-phase cell counting
// in the cipher, so the ECDH / sponge / packing split quoted in this tree is
// computed from ZisK's cost table rather than measured. Instrumenting it needs
// its own diagnostic mode, because the committed output region is already at
// 248 of 256 bytes in the keccak-sites build.

#pragma once

#include <category/core/config.hpp>
#include <zkvm/guest/l2_cipher.hpp>

#include <concepts>
#include <optional>
#include <span>
#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

/// What the proved path calls. A suite is a type with two associated types and
/// two static functions; the concept is written as the call expressions rather
/// than as signatures so that a suite is free to take its own types by
/// reference or by value.
///
/// `Context` is the block-constant half of the suite's inputs, built once a
/// block from compiled deployment constants and header fields (l2_config.hpp).
/// It is a PARAMETER of everything below rather than a global, so a test can
/// inject one without a deployment.
///
/// `Secret` is the operator secret, obtainable only from `bind_secret`.
template <typename S>
concept L2CipherSuite = requires(
    typename S::Context const &ctx, typename S::Secret const &secret,
    std::span<unsigned char const, 32> const witness_secret,
    std::span<unsigned char const> const leaf,
    std::vector<unsigned char> &plain) {
    /// Names the suite AND its protocol version, as
    /// "monad-l2/ecdh-poseidon2/v1/" does.
    /// Reaches the sponge as its domain label, so two suites over one
    /// permutation are separated oracles, and reaches a build's diagnostics so
    /// a measurement can say which suite produced it.
    { S::LABEL } -> std::convertible_to<std::string_view>;

    /// Parses the witness's 32 secret bytes AND checks them against `ctx`.
    /// Nullopt when they are not the secret this context names -- a malformed
    /// witness, which the caller turns into a halt, not a rejection.
    {
        S::bind_secret(ctx, witness_secret)
    } -> std::same_as<std::optional<typename S::Secret>>;

    /// Verifies and decrypts one leaf, resizing `plain` to the plaintext.
    /// False is a deterministic rejection of that entry, never an error to
    /// report.
    { S::decrypt(ctx, secret, leaf, plain) } -> std::same_as<bool>;
};

// ---- Selection -------------------------------------------------------------
//
// cmake/l2.cmake validates MONAD_ZKVM_L2_CIPHER against the suites it knows and
// defines exactly one MONAD_L2_CIPHER_* macro from the name. An unknown name
// fails configuration there, with the list in the message -- which is why the
// #error below is reachable only if that mapping and these arms have drifted
// apart, and says so rather than repeating the list.
//
// Outside an L2 build there is no macro and the default is used. That is not a
// loophole: the L2 unit tests are built in a plain host tree, deliberately, so
// that the cipher and the decoder are testable without a deployment's eight
// required values. Nothing is proved in such a build.

#if defined(MONAD_L2_CIPHER_ECDH_POSEIDON2)
/// ECDH on secp256k1, Poseidon2 masks over Goldilocks, a Poseidon2 tag over the
/// ciphertext. See l2_cipher.hpp.
using L2Cipher = L2EcdhPoseidon2;
#elif !defined(MONAD_ZKVM_L2)
// Host test build: the default, per the note above.
using L2Cipher = L2EcdhPoseidon2;
#else
    #error                                                                     \
        "MONAD_ZKVM_L2 build with no known MONAD_L2_CIPHER_* macro -- cmake/l2.cmake and this file disagree about the suite names"
#endif

/// Checked here rather than at each use, so an incomplete suite names itself
/// once instead of failing at whichever call site the compiler reaches first.
static_assert(
    L2CipherSuite<L2Cipher>,
    "the selected MONAD_ZKVM_L2_CIPHER does not provide the L2CipherSuite "
    "interface -- see the concept above for the two entry points and the two "
    "associated types it is missing");

MONAD_NAMESPACE_END
