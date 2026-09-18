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

// The end-of-block message anchor: the merkle root of every message
// NamespaceSpoke recorded during the block, which the operator relays onto the
// L1 hub through submitStateSignature.
//
// It lives in category/execution/ethereum rather than in zkvm/guest for one
// reason: the rule has to match OpenZeppelin's MerkleProof bit for bit, and the
// guest and the node both need it. A keccak rule duplicated across two
// translation units that no build step keeps in step is the likeliest way this
// breaks.
//
// The spoke address and its storage slot are PARAMETERS and not constants here.
// That keeps the deployment out of a header the node also compiles, and it is
// what makes the harvest testable against a fabricated receipt.

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <cstdint>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;

#ifdef MONAD_ZKVM_L2
    #ifndef MONAD_L2_NAMESPACE_SPOKE
        #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_SPOKE=0x<40 hex>"
    #endif
    #ifndef MONAD_L2_PENDING_SLOT
        #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_PENDING_SLOT=<n>"
    #endif

/// The NamespaceSpoke deployment, and the storage slot of its
/// `_pendingNamespaceMessages` array.
///
/// They live here, in the shared anchor header, and not with the cipher's
/// configuration under zkvm/guest: emptying that array is a consensus rule, so
/// the node's epilogue needs these too, and the node has no business including
/// a guest header. No defaults -- a guest pointed at the wrong spoke emits
/// proofs the L1 hub accepts, so a missing value has to stop the build.
///
/// The slot must come from `forge inspect NamespaceSpoke storage-layout`
/// against the deployed contract. Reading the source gives 1 -- the two
/// immutables occupy no slot and INamespaceSpoke is an interface, so `_nonce`
/// is slot 0 -- but a guess here clears somebody else's storage.
inline constexpr Address L2_NAMESPACE_SPOKE = MONAD_L2_NAMESPACE_SPOKE;
inline constexpr std::uint64_t L2_PENDING_SLOT = MONAD_L2_PENDING_SLOT;
#endif

/// NamespaceSpoke's outbound-message event. `from` and `to` are indexed, so a
/// log carries three topics and the rest sits in its data section.
inline constexpr bytes32_t NAMESPACE_MESSAGE_RECORDED_TOPIC =
    abi_encode_event_signature(
        "NamespaceMessageRecorded(address,address,bytes,uint256,bytes32)");
static_assert(
    NAMESPACE_MESSAGE_RECORDED_TOPIC ==
    0x2013a1d0b9a3c17ead41b5433daeef9f5b301d7abece37308528e70113a678df_bytes32);

/// Head words in the event's data section: the offset of `data`'s tail, then
/// `nonce`, then `messageHash`. `data` is the only dynamic parameter and it
/// comes first, so Solidity emits that offset as 0x60 and nothing else.
inline constexpr std::size_t NAMESPACE_LOG_HEAD_WORDS = 3;
inline constexpr std::size_t NAMESPACE_LOG_DATA_OFFSET = 0x60;
/// messageHash sits at the third head word.
inline constexpr std::size_t NAMESPACE_LOG_HASH_OFFSET = 64;
/// Three head words plus the tail's own length word, even for empty `data`.
inline constexpr std::size_t NAMESPACE_LOG_MIN_SIZE = 128;

/// Message hashes recorded by `spoke` during this block, in log order -- which
/// is the order the contract pushed them, so the leaf set and its pending array
/// coincide.
///
/// The receipts have already been checked against the header's receipts root by
/// the time this runs, so the leaves are canonical rather than prover-chosen.
///
/// A log at `spoke` carrying this topic that does not decode is NOT skipped: it
/// means the deployed contract no longer matches this code, and skipping it
/// would produce a well-formed anchor over the wrong leaf set -- which the L1
/// hub would accept. It fails the block, the way extract_deposit_requests does
/// for the same reason. Logs that match neither the address nor the topic are
/// ignored silently.
Result<std::vector<bytes32_t>> collect_namespace_messages(
    std::span<Receipt const> receipts, Address const &spoke);

/// The root of the sorted-pair merkle tree OpenZeppelin's MerkleProof verifies
/// against, reproducing NamespaceSpoke's MerkleTreeLib.root: every level is
/// keccak256(min(a,b) || max(a,b)) over adjacent pairs, and a trailing odd node
/// is promoted to the next level unchanged. A single leaf is its own root.
///
/// THIS IS NOT the Ethereum ordered trie. zkvm/guest/body_roots.hpp's
/// ordered_trie_root is a different rule for a different job, and a proof built
/// against one does not verify against the other. Do not "simplify" the pair
/// ordering: it is what the L1 contract computes.
///
/// Empty gives bytes32_t{}. MerkleTreeLib.root reverts on an empty array, but
/// finalizeNamespaceMessages never reaches it -- its length==0 early return
/// yields bytes32(0), and that is the branch being mirrored.
///
/// Exactly `n - 1` keccak calls for `n` leaves: each hash takes two nodes and
/// gives one, and a promotion takes none. `leaves` is reduced IN PLACE.
bytes32_t sorted_pair_merkle_root(std::vector<bytes32_t> &leaves);

/// Zeroes `spoke`'s pending-message array the way `delete` does on a Solidity
/// bytes32[]: every element slot and then the length slot. `slot` is the
/// array's declared slot; elements live at keccak256(u256_be(slot)) + i.
///
/// `expected_length` is the harvest's leaf count, and the mismatch assertion is
/// the highest-value check in this whole mechanism: both sides come from
/// canonical data -- the length through canonical execution from the pre-state
/// trie, the count from receipts the header commits to -- so a disagreement
/// means the rule is wrong, not that the witness is. It is also the only thing
/// that catches the guest's leaf set and the contract's pending set drifting
/// apart, which is exactly what the L1 hub cannot detect.
/// Storage key of element `i` of a Solidity bytes32[] declared at `slot`:
/// keccak256(u256_be(slot)) + i. Exposed on its own so the derivation -- the
/// only part of the clear with anything to get wrong -- is testable without
/// standing up a State.
bytes32_t
namespace_pending_element_key(std::uint64_t slot, std::uint64_t index);

void clear_pending_namespace_messages(
    State &state, Address const &spoke, std::uint64_t slot,
    std::uint64_t expected_length);

MONAD_NAMESPACE_END
