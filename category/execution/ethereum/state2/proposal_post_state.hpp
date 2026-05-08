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

#include <ankerl/unordered_dense.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

// Account map keyed by Address. nullopt means the account was deleted (or
// does not exist) for the proposal at hand. Populated by
// CommitBuilder::add_state_deltas (one entry per touched account) and drained
// via CommitBuilder::take_proposal_post_state.
using AccountPostState =
    ankerl::unordered_dense::segmented_map<Address, std::optional<Account>>;

// Storage leaf map keyed by StorageKey{addr, incarnation, key}. The key
// granularity matches the trie's storage subtree: slot_key for slot
// encoding, page_key for page encoding. The value is the encoded leaf
// bytes the underlying trie would return for read_storage at that key
// (zeroless bytes for slot, encode_storage_page output for page). An
// empty byte_string means "no entry / deleted" — this is unambiguous for
// both encodings since the zero slot's compact form is also empty bytes
// and an empty page's encoding is never written to the trie.
using StoragePostState = ankerl::unordered_dense::segmented_map<
    StorageKey, byte_string, BytesHashCompare<StorageKey>>;

struct ProposalPostState
{
    AccountPostState accounts;
    StoragePostState storage;
};

MONAD_NAMESPACE_END
