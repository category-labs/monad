// Copyright (C) 2025 Category Labs, Inc.
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

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>

#include <ankerl/unordered_dense.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

// Account map keyed by Address. nullopt means the account was deleted (or
// does not exist) for the proposal at hand.
using AccountOverlay =
    ankerl::unordered_dense::segmented_map<Address, std::optional<Account>>;

// Storage leaf map keyed by StorageKey{addr, incarnation, key}. The key
// granularity matches the trie's storage subtree: slot_key for slot
// encoding, page_key for page encoding. The value is the encoded leaf
// bytes the underlying trie would return for read_storage at that key
// (zeroless bytes for slot, encode_storage_page output for page). An
// empty byte_string means "no entry / deleted" - this is unambiguous for
// both encodings since the zero slot's compact form is also empty bytes
// and an empty page's encoding is never written to the trie.
using LeafOverlay = ankerl::unordered_dense::segmented_map<
    StorageKey, byte_string, BytesHashCompare<StorageKey>>;

struct ProposalOverlays
{
    AccountOverlay accounts;
    LeafOverlay storage;
};

// Walks the state deltas and produces an AccountOverlay along with a
// slot-encoded LeafOverlay (one entry per storage slot delta). Used by
// the ethereum runloop and by anyone committing without a custom storage
// builder.
ProposalOverlays from_slot_state_deltas(StateDeltas const &);

// Builds an AccountOverlay from state deltas and pairs it with a
// caller-provided LeafOverlay. For page mode, the LeafOverlay comes from
// MonadCommitBuilder::take_leaf_overlay(): one entry per touched page,
// keyed by (addr, inc, page_key) with value encode_storage_page(page).
ProposalOverlays
from_page_state_deltas(StateDeltas const &, LeafOverlay storage);

MONAD_NAMESPACE_END
