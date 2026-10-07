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

// End-of-block Merkle root of NamespaceSpoke messages, relayed to L1 via
// submitStateSignature. Shared by node and guest to match MerkleProof. The
// spoke address and storage slot are parameters for deployment and tests.

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
    #ifndef MONAD_L2_DOMAIN_SPOKE
        #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_SPOKE=0x<40 hex>"
    #endif
    #ifndef MONAD_L2_PENDING_SLOT
        #error "MONAD_ZKVM_L2 requires -DMONAD_ZKVM_L2_PENDING_SLOT=<n>"
    #endif

/// NamespaceSpoke address and pending-array slot, shared by node and guest
/// because clearing the array changes consensus state. Both are required.
/// Obtain the slot from `forge inspect NamespaceSpoke storage-layout` for the
/// deployed contract; an incorrect slot clears unrelated storage.
inline constexpr Address L2_DOMAIN_SPOKE = MONAD_L2_DOMAIN_SPOKE;
inline constexpr std::uint64_t L2_PENDING_SLOT = MONAD_L2_PENDING_SLOT;
#endif

/// Vendored NamespaceSpoke event (e6012d8cebf4): from/to are indexed. The
/// current DomainMessageRecorded event has the same parameters but topic
/// 0x8f2b779508ea0cb38e5b78dbe9c7a04c3ce671ba697fdce1a46dc794e2dd650e. That
/// topic is not harvested here; the pending-length check detects the
/// mismatch. Re-vendoring also requires the new access controls; see
/// CONFORMANCE.md.
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

/// Collect message hashes from executed receipts in log order, matching the
/// pending-array insertion order. Ignore other addresses/topics, but reject
/// malformed matching logs to avoid publishing an incomplete anchor.
Result<std::vector<bytes32_t>> collect_domain_messages(
    std::span<Receipt const> receipts, Address const &spoke);

/// NamespaceSpoke/MerkleProof root: hash adjacent sorted pairs with
/// keccak256(min(a,b) || max(a,b)); promote an odd final node unchanged. A
/// singleton is its own root; empty returns zero, matching
/// finalizeNamespaceMessages. This is not an ordered-trie root. Reduces
/// leaves in place using n-1 hashes for nonempty input.
bytes32_t sorted_pair_merkle_root(std::vector<bytes32_t> &leaves);

/// Pending-array element key: keccak256(u256_be(slot)) + i. Exposed for
/// independent testing. clear_pending_domain_messages zeroes every element
/// and then the length, matching Solidity delete. Its length check requires
/// the stored pending count to equal the number of harvested messages.
bytes32_t domain_pending_element_key(std::uint64_t slot, std::uint64_t index);

void clear_pending_domain_messages(
    State &state, Address const &spoke, std::uint64_t slot,
    std::uint64_t expected_length);

MONAD_NAMESPACE_END
