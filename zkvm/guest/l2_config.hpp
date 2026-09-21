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

// The L2's deployment constants, every one a required CMake input with NO
// default.
//
// Deliberately no defaults: a guest that anchors the wrong contract, or
// decrypts under the wrong operator key, would produce a proof the L1 hub
// accepts. A placeholder would make that a silent misconfiguration; an
// #error makes it a build failure that names the missing value.
//
// zkvm/guest/CMakeLists.txt checks them and fails configuration with the same
// list, so the usual case is a CMake message rather than a compiler one.

#pragma once

#ifndef MONAD_ZKVM_L2
    #error "l2_config.hpp is for MONAD_ZKVM_L2 builds only"
#endif

#ifndef MONAD_L2_CHAIN_ID
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_CHAIN_ID=<n>"
#endif
#ifndef MONAD_L2_NAMESPACE_ID
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_NAMESPACE_ID=<n>"
#endif
#ifndef MONAD_L2_REVISION
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_REVISION=<MONAD_ETH_*>"
#endif
#ifndef MONAD_L2_OPERATOR_PK_X
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_OPERATOR_PK_X=0x<64 hex>"
#endif
#ifndef MONAD_L2_OPERATOR_PK_ODD
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_OPERATOR_PK_ODD=<0|1>"
#endif
#ifndef MONAD_L2_EPOCH_BLOCKS
    #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_EPOCH_BLOCKS=<n>"
#endif

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/namespace_anchor.hpp>
#include <category/vm/evm/revision.h>
#include <zkvm/guest/l2_cipher_suite.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

/// Bumped whenever anything about the encryption changes -- the permutation
/// instance, the sponge mode, the context layout, the leaf format. It is
/// absorbed into A, so two versions never derive the same key.
///
/// It does not select a suite. Which suite is compiled is MONAD_ZKVM_L2_CIPHER
/// (cmake/l2.cmake); this is the version WITHIN one, and a suite carries both
/// in its LABEL so neither can be bumped without the other taking effect.
inline constexpr std::uint64_t L2_CIPHER_VERSION = 1;

inline constexpr std::uint64_t L2_CHAIN_ID = MONAD_L2_CHAIN_ID;
inline constexpr std::uint64_t L2_NAMESPACE_ID = MONAD_L2_NAMESPACE_ID;

/// A constant, not a fork schedule: an L2 that starts at one revision has no
/// schedule to consult, and carrying one would be a second place for the
/// revision to be decided.
inline constexpr monad_eth_revision L2_REVISION = MONAD_L2_REVISION;

/// The operator's public key, as a compressed point split into its
/// x-coordinate and the parity of y. Split rather than given as 33 hex bytes
/// so the existing _bytes32 literal can carry it with no parser.
///
/// The x-coordinate is 32 BIG-ENDIAN bytes, which is what SEC1 means by an
/// x-coordinate and what a _bytes32 literal spells. Said explicitly because a
/// byte order that lives only in the reader is how these go wrong: to_bytes on
/// a uint256_t would have given the other order, silently.
inline constexpr bytes32_t L2_OPERATOR_PK_X = MONAD_L2_OPERATOR_PK_X;
inline constexpr bool L2_OPERATOR_PK_ODD = MONAD_L2_OPERATOR_PK_ODD != 0;

/// Blocks per epoch, which is how the epoch in A is derived. A GUESS at the
/// protocol's intent: the epoch is a field of the context the scheme specifies
/// but does not define, and this is the cheapest definition that is a function
/// of the header alone -- so it cannot be the prover's to choose. Confirm it
/// before this is anything but a prototype.
inline constexpr std::uint64_t L2_EPOCH_BLOCKS = MONAD_L2_EPOCH_BLOCKS;

/// The block-constant cipher context. Every field is a compiled constant or a
/// header field, so nothing in it is the prover's.
///
/// Declared in terms of the selected suite, so this declaration survives a
/// change of suite even though its body does not: what a context holds is the
/// suite's business, and turning deployment constants into one is this file's.
L2Cipher::Context l2_cipher_context(BlockHeader const &header);

MONAD_NAMESPACE_END
