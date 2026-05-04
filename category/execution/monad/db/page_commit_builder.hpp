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

#include <memory>

MONAD_NAMESPACE_BEGIN

struct Db;

class PageCommitBuilder : public CommitBuilder
{
    Db &db_;

public:
    PageCommitBuilder(uint64_t block_number, Db &db);

    // Materializes pages from slot deltas, writes per-page updates, and
    // populates the inherited `proposal_post_state_` with page-keyed
    // storage_page_t entries. Use `take_proposal_post_state()` after this to
    // consume the result.
    CommitBuilder &add_state_deltas(StateDeltas const &) override;

    bool is_page_encoded() const override
    {
        return true;
    }
};

MONAD_NAMESPACE_END
