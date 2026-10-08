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

// Required deployment constants, with no defaults. CMake and these guards
// reject missing values to avoid silently targeting the wrong deployment.

#pragma once

#ifndef MONAD_ZKVM_L2
    #error "l2_config.hpp is for MONAD_ZKVM_L2 builds only"
#endif

#ifndef MONAD_L2_CHAIN_ID
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_CHAIN_ID=<n>"
#endif
#ifndef MONAD_L2_REVISION
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_REVISION=<MONAD_FOUR+>"
#endif
#ifndef MONAD_L2_OPERATOR_PK_X
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_OPERATOR_PK_X=0x<64 hex>"
#endif
#ifndef MONAD_L2_OPERATOR_PK_ODD
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_OPERATOR_PK_ODD=<0|1>"
#endif

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/domain_anchor.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/revision.h>
#include <zkvm/guest/l2_cipher_suite.hpp>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

/// Version within the selected cipher suite. Bump for changes to the
/// permutation, sponge, context or wire format; it binds key derivation.
/// MONAD_ZKVM_L2_CIPHER selects the suite separately.
inline constexpr std::uint64_t L2_CIPHER_VERSION = 1;

inline constexpr std::uint64_t L2_CHAIN_ID = MONAD_L2_CHAIN_ID;
/// A constant, not a fork schedule: an L2 that starts at one revision has no
/// schedule to consult, and carrying one would be a second place for the
/// revision to be decided.
inline constexpr monad_revision L2_REVISION = MONAD_L2_REVISION;

/// MONAD_FOUR or later. Below it ReserveBalance::init_from_tx turns its own
/// tracking off, so the reserve rules the client applies would not be applied
/// here and the two would compute different states from the same block. It is
/// also well past the Merge, which is what keeps apply_block_reward from
/// minting to prover-chosen addresses.
static_assert(
    L2_REVISION >= MONAD_FOUR,
    "below MONAD_FOUR the reserve balance stops tracking, and the guest would "
    "diverge from the client on any transaction that dips into it");

/// Compressed operator key: 32-byte big-endian x and y parity, split to use
/// the existing _bytes32 literal without a parser.
inline constexpr bytes32_t L2_OPERATOR_PK_X = MONAD_L2_OPERATOR_PK_X;
inline constexpr bool L2_OPERATOR_PK_ODD = MONAD_L2_OPERATOR_PK_ODD != 0;

/// Commitment to the witness blinding seed. Never embed the seed itself: the
/// ELF is public.
inline constexpr bytes32_t L2_SALT_COMMITMENT = MONAD_L2_SALT_COMMITMENT;

/// The commitment to a blinder secret: keccak256 of it, or under
/// MONAD_ZKVM_L2_HASH=poseidon2 the Poseidon2 sponge over a label and it. The
/// generator prints it for a deployment (--salt-commitment) and the guest
/// checks the witness's secret against the compiled one.
bytes32_t l2_salt_commitment(std::span<unsigned char const, 32> salt_secret);

/// Derive a blinder with the chain hash over label, secret, domain and block
/// number. The domain separates reused seeds; the height prevents equal
/// states at different heights from publishing equal commitments.
///
/// Blinding prevents offline guesses against roots inferred from public
/// activity. Derivation requires no stored per-block randomness, but leaking
/// the seed exposes every historical blinder.
bytes32_t l2_state_salt(
    std::span<unsigned char const, 32> salt_secret, std::uint64_t block_number);

/// Blind the state root for publication. L1 stores/compares this commitment;
/// message proofs use the separate anchor. The client reopens it using the
/// same root, height and private seed as the guest.
bytes32_t l2_state_commitment(
    std::span<unsigned char const, 32> salt_secret, std::uint64_t block_number,
    bytes32_t const &state_root);

/// Build the selected suite's context from deployment constants and, if
/// needed by that suite, the header.
L2Cipher::Context l2_cipher_context(BlockHeader const &header);

MONAD_NAMESPACE_END
