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
#include <category/execution/ethereum/state2/block_state.hpp>

#include <map>
#include <memory>

MONAD_NAMESPACE_BEGIN

struct Db;

class PageCommitBuilder final : public CommitBuilder
{
    Db &db_;
    // non-null when multi_block_cache_active: enables last_access bumps and
    // histogram maintenance
    BlockAccessSets const *access_;
    // histogram weight deltas by (kind, bucket block); ordered so the emitted
    // updates are reproducible
    std::map<std::pair<PricingKind, uint64_t>, int64_t> bucket_deltas_;

    void bump_account(std::optional<Account> const &pre, Account &post);
    void add_pricing_updates();

public:
    PageCommitBuilder(
        uint64_t block_number, Db &db,
        BlockAccessSets const *access = nullptr);

    // Materializes pages from slot deltas, writes per-page updates, and
    // populates the inherited `proposal_post_state_` with page-keyed
    // storage_page_t entries. Use `take_proposal_post_state()` after this to
    // consume the result.
    CommitBuilder &add_state_deltas(StateDeltas const &) override;
};

// Selects the builder matching the db encoding: PageCommitBuilder for a
// page-encoded db, plain CommitBuilder otherwise.
std::unique_ptr<CommitBuilder> make_commit_builder(
    uint64_t block_number, Db &db, BlockAccessSets const *access = nullptr);

MONAD_NAMESPACE_END
