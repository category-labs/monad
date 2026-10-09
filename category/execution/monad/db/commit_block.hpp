// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/vm/evm/traits.hpp>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct CallFrame;
struct Receipt;
struct Transaction;
struct Withdrawal;
struct Db;

// Per-block ancillary inputs forwarded to the CommitBuilder. State deltas are
// passed separately because the builder's add_state_deltas override (slot or
// page, chosen by make_commit_builder from the db's encoding) consumes them.
struct BlockCommitAncillaries
{
    Code const &code;
    std::vector<Receipt> const &receipts;
    std::vector<Transaction> const &transactions;
    std::vector<Address> const &senders;
    std::vector<std::vector<CallFrame>> const &call_frames;
    std::vector<BlockHeader> const &ommers;
    std::optional<std::vector<Withdrawal>> const &withdrawals;
};

// Commit one block to `db`. The db's storage encoding must match the block's
// revision (slot before MIP-8, page after); asserted on entry.
template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_block(
    Db &db, bytes32_t const &block_id, BlockHeader const &header,
    StateDeltas const &state, BlockCommitAncillaries const &anc);

MONAD_NAMESPACE_END
