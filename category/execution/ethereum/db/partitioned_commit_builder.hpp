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

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <cstdint>
#include <deque>

MONAD_NAMESPACE_BEGIN

struct Db;

// Writes state deltas in the EIP-8297 partitioned layout
// (partitioned_layout.hpp). An account is one leaf at its header stem key;
// its storage zone leaves hang off its storage stem, a nested root with an
// empty value, so deleting or recreating an account is one erase or one
// incarnation update per stem. The storage stem of an account only exists
// once a slot outside the header was written, so the builder asks the db
// whether it exists before erasing it.
class PartitionedCommitBuilder final : public CommitBuilder
{
    Db &db_;
    std::deque<mpt::Nibbles> nibbles_alloc_;
    std::deque<bytes32_t> value_alloc_;

    mpt::Update &leaf_update(mpt::Nibbles key, bytes32_t const &value);
    mpt::Update &erase_update(mpt::Nibbles key);

public:
    PartitionedCommitBuilder(uint64_t block_number, Db &db);

    CommitBuilder &add_state_deltas(StateDeltas const &) override;
};

MONAD_NAMESPACE_END
