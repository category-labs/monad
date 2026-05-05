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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/proposal_overlays.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>

#include <utility>

MONAD_NAMESPACE_BEGIN

ProposalOverlays from_slot_state_deltas(StateDeltas const &state_deltas)
{
    ProposalOverlays result;
    for (auto const &[addr, delta] : state_deltas) {
        result.accounts[addr] = delta.account.second;
        if (!delta.account.second.has_value()) {
            continue;
        }
        auto const inc = delta.account.second->incarnation;
        for (auto const &[key, slot_delta] : delta.storage) {
            StorageKey const sk{addr, inc, key};
            result.storage[sk] = compact_storage_view(slot_delta.second);
        }
    }
    return result;
}

ProposalOverlays
from_page_state_deltas(StateDeltas const &state_deltas, LeafOverlay storage)
{
    ProposalOverlays result{.accounts = {}, .storage = std::move(storage)};
    for (auto const &[addr, delta] : state_deltas) {
        result.accounts[addr] = delta.account.second;
    }
    return result;
}

MONAD_NAMESPACE_END
