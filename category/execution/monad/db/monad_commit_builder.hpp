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

#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/proposal_overlays.hpp>
#include <category/vm/evm/monad/revision.h>

#include <memory>
#include <utility>

MONAD_NAMESPACE_BEGIN

class PageStorageBroker;

class MonadCommitBuilder : public CommitBuilder
{
    PageStorageBroker &broker_;
    // Populated during add_state_deltas: one entry per touched page,
    // keyed by (addr, inc, page_key) with value encode_storage_page(page).
    // Empty byte_string for an emptied page. The runloop hands this off
    // to ProposalOverlays so DbCache caches page-shaped entries that the
    // PageStorageBroker can read back.
    LeafOverlay leaf_overlay_;

public:
    MonadCommitBuilder(uint64_t block_number, PageStorageBroker &broker);

    CommitBuilder &add_state_deltas(StateDeltas const &) override;

    LeafOverlay take_leaf_overlay() &&
    {
        return std::move(leaf_overlay_);
    }

    byte_string_view state_marker() const override;
};

MONAD_NAMESPACE_END
