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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_block(
    Db &primary_db, Db *secondary_db, bytes32_t const &block_id,
    BlockHeader const &header, StateDeltas const &state,
    BlockCommitAncillaries const &anc)
{
    auto add_common_deltas = [&](CommitBuilder &b) {
        b.add_code(anc.code)
            .add_receipts(anc.receipts)
            .add_transactions(anc.transactions, anc.senders)
            .add_call_frames(anc.call_frames)
            .add_ommers(anc.ommers);
        if (anc.withdrawals.has_value()) {
            b.add_withdrawals(anc.withdrawals.value());
        }
    };

    // Dual-write migration path. Db1 (primary, slot) and Db2 (*secondary_db,
    // page) write the same data to every table; the only difference is
    // state encoding. state_deltas is added separately to each builder so
    // MonadCommitBuilder's override can kick in for Db2; everything else
    // goes through the shared helper.

    // `correct_db` is the "source of truth" Db the header populator reads
    // roots from. Both the Db1 and Db2 commits call populate_header via
    // this same pointer, so both end up with identical block headers. The
    // pointer is assigned just before commits run (see the if constexpr
    // block below). Non-state roots are the same on Db1 and Db2 (same
    // inputs, only state encoding differs), so the choice only really
    // changes which state_root is stamped into the header.
    Db *correct_db = nullptr;
    auto populate_header = [&](BlockHeader &h) {
        MONAD_ASSERT(correct_db != nullptr);
        h.receipts_root = correct_db->receipts_root();
        h.state_root = correct_db->state_root();
        h.withdrawals_root = correct_db->withdrawals_root();
        h.transactions_root = correct_db->transactions_root();
        h.gas_used = anc.receipts.empty() ? 0 : anc.receipts.back().gas_used;
        h.logs_bloom = compute_bloom(anc.receipts);
        h.ommers_hash = compute_ommers_hash(anc.ommers);
    };

    if (secondary_db == nullptr) {
        std::unique_ptr<CommitBuilder> builder;
        if constexpr (traits::monad_rev() >= MONAD_NEXT) {
            builder =
                std::make_unique<PageCommitBuilder>(header.number, primary_db);
        }
        else {
            builder = std::make_unique<CommitBuilder>(header.number);
        }
        builder->add_state_deltas(state);
        add_common_deltas(*builder);
        correct_db = &primary_db;
        primary_db.commit(block_id, *builder, header, state, populate_header);
        return;
    }

    CommitBuilder builder(header.number);
    builder.add_state_deltas(state);
    add_common_deltas(builder);

    PageCommitBuilder builder2(header.number, *secondary_db);
    builder2.add_state_deltas(state);
    add_common_deltas(builder2);

    // Whichever Db owns the canonical state_root commits first, so its
    // state_root is live when the later commit's populate_header runs.
    //
    // Pre-fork: Db1 is canonical. Commit Db1 first with correct_db=&primary_db;
    // Db2 commits after, reading Db1's now-live roots.
    //
    // Post-fork: Db2 owns the page-based state_root. Commit Db2 first with
    // correct_db=secondary_db; Db1 commits after, reading Db2's roots.
    if constexpr (traits::monad_rev() >= MONAD_NEXT) {
        correct_db = secondary_db;
        secondary_db->commit(
            block_id, builder2, header, state, populate_header);
        primary_db.commit(block_id, builder, header, state, populate_header);
    }
    else {
        correct_db = &primary_db;
        primary_db.commit(block_id, builder, header, state, populate_header);
        secondary_db->commit(
            block_id, builder2, header, state, populate_header);
    }
}

EXPLICIT_MONAD_TRAITS(commit_block);

MONAD_NAMESPACE_END
