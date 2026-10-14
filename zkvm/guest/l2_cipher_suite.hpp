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

// Compile-time cipher interface and selection. Suites own wire format, curve,
// sponge, tag and packing; callers exchange bytes. Unselected suites are not
// linked.
//
// All suites must preserve these protocol rules:
// - decrypt failures deterministically consume and skip one entry, without
// state changes, receipts or a guest halt.
// - bind_secret rejects witness secrets not bound to the supplied context.
// - Outcomes depend only on leaf, secret and context.
//
// Compare suites using separate ELFs under ziskemu. Per-phase cipher costs in
// this tree are cost-table estimates, not measured breakdowns.

#pragma once

#include <category/core/config.hpp>
#include <zkvm/guest/l2_cipher.hpp>
#include <zkvm/guest/l2_plaintext_suite.hpp>

#include <concepts>
#include <optional>
#include <span>
#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

/// Suite API: Context and Secret plus bind_secret and decrypt. Context is
/// supplied explicitly for deployment-free tests. bind_secret validates the
/// secret before decoding; the concept permits value or reference arguments.
template <typename S>
concept L2CipherSuite = requires(
    typename S::Context const &ctx, typename S::Secret const &secret,
    std::span<unsigned char const, 32> const witness_secret,
    std::span<unsigned char const> const leaf,
    std::vector<unsigned char> &plain) {
    /// Suite/version label used for sponge domain separation and diagnostics.
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

// cmake/l2.cmake selects exactly one MONAD_L2_CIPHER_* macro. Unknown names
// fail configuration; the error below catches mismatched selection arms.
// Plain host tests use the default without deployment constants.

#if defined(MONAD_L2_CIPHER_ECDH_POSEIDON2)
/// ECDH on secp256k1, Poseidon2 masks over Goldilocks, a Poseidon2 tag over the
/// ciphertext. See l2_cipher.hpp.
using L2Cipher = L2EcdhPoseidon2;
#elif defined(MONAD_L2_CIPHER_PLAINTEXT)
/// No encryption: the measurement control. See l2_plaintext_suite.hpp.
using L2Cipher = L2PlaintextSuite;
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
