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
#include <category/execution/ethereum/db/account_key.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/monad/db/storage_page.hpp>

#include <ankerl/unordered_dense.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

// Account map keyed by AccountKey{addr, ns}. nullopt means the account was
// deleted (or does not exist) for the proposal at hand. Populated by
// CommitBuilder::add_state_deltas (one entry per touched account) and drained
// via CommitBuilder::take_proposal_post_state.
using AccountPostState = ankerl::unordered_dense::segmented_map<
    AccountKey, std::optional<Account>, BytesHashCompare<AccountKey>>;

// Storage leaf map keyed by StorageKey{addr, incarnation, key, ns}. The key
// granularity matches the trie's storage subtree: slot_key (single slot at
// index 0) for slot mode, page_key (full page) for page mode. The key being
// present marks "touched by this proposal"; an empty storage_page_t means every
// slot in that entry is zero (deleted), which is stored as a present entry
// rather than absent.
using StoragePostState = ankerl::unordered_dense::segmented_map<
    StorageKey, storage_page_t, BytesHashCompare<StorageKey>>;

struct ProposalPostState
{
    AccountPostState accounts;
    StoragePostState storage;
};

using NamespacedProposalPostState =
    ankerl::unordered_dense::segmented_map<uint64_t, ProposalPostState>;

MONAD_NAMESPACE_END
