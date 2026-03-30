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

#include <category/core/byte_string.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/storage_encoding.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>

#include <ankerl/unordered_dense.h>

#include <optional>

MONAD_NAMESPACE_BEGIN

using AccountOverlay =
    ankerl::unordered_dense::segmented_map<Address, std::optional<Account>>;

using LeafOverlay = ankerl::unordered_dense::segmented_map<
    StorageKey, byte_string, BytesHashCompare<StorageKey>>;

struct ProposalOverlays
{
    AccountOverlay accounts;
    LeafOverlay storage;

    // Build overlays from state deltas. If leaf_overlay is provided (from
    // a commit builder), it is used directly. Otherwise, slot-format leaf
    // entries are built from the deltas.
    static ProposalOverlays from_state_deltas(
        StateDeltas const &state_deltas, LeafOverlay *leaf_overlay = nullptr)
    {
        LeafOverlay local_leaves;
        AccountOverlay accounts;
        for (auto it = state_deltas.cbegin(); it != state_deltas.cend(); ++it) {
            auto const &addr = it->first;
            auto const &delta = it->second;
            accounts[addr] = delta.account.second;

            if (!leaf_overlay && delta.account.second.has_value()) {
                auto const inc = delta.account.second->incarnation;
                for (auto it2 = delta.storage.cbegin();
                     it2 != delta.storage.cend();
                     ++it2) {
                    auto const &key = it2->first;
                    auto const &val = it2->second.second;
                    StorageKey const sk{addr, inc, key};
                    local_leaves[sk] = val == bytes32_t{}
                                           ? byte_string{}
                                           : encode_storage_eth(val);
                }
            }
        }
        return {
            std::move(accounts),
            leaf_overlay ? std::move(*leaf_overlay) : std::move(local_leaves)};
    }
};

MONAD_NAMESPACE_END
