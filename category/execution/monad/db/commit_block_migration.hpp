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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/vm/evm/traits.hpp>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct CallFrame;
struct Db;
struct Receipt;
struct Transaction;
struct Withdrawal;
class PageStorageBroker;

// Per-block ancillary inputs that the dual commit path forwards to the
// shared CommitBuilder helpers. State deltas are passed separately because
// each builder (slot for Db1, page for Db2) has its own add_state_deltas
// override that needs the same StateDeltas instance.
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

// Commits a single Monad block. The block is always mirrored into Db2 (page
// encoded) via the supplied PageStorageBroker; the secondary db is mandatory
// during the migration. The order of the two commits depends on which Db
// owns the canonical state_root for the active monad revision. Pre-fork
// (< MONAD_NEXT) Db1 commits first; post-fork Db2 commits first so its
// page based state_root is live when populate_header runs for Db1. Both Dbs
// end up with the same canonical block header.
template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_block(
    Db &primary_db, Db &secondary_db, PageStorageBroker &page_broker,
    bytes32_t const &block_id, bytes32_t const &parent_block_id,
    bool is_first_block, BlockHeader const &header, StateDeltas const &state,
    BlockCommitAncillaries const &anc);

MONAD_NAMESPACE_END
