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
#include <category/execution/monad/db/commit_block.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_block(
    Db &db, bytes32_t const &block_id, BlockHeader const &header,
    StateDeltas const &state, BlockCommitAncillaries const &anc)
{
    // make_commit_builder picks the slot or page builder from the db's
    // encoding, which must match the block's revision.
    MONAD_ASSERT(db.is_page_encoded() == traits::mip_8_active());
    auto builder = make_commit_builder(header.number, db);
    builder->add_state_deltas(state)
        .add_code(anc.code)
        .add_receipts(anc.receipts)
        .add_transactions(anc.transactions, anc.senders)
        .add_call_frames(anc.call_frames)
        .add_ommers(anc.ommers);
    if (anc.withdrawals.has_value()) {
        builder->add_withdrawals(anc.withdrawals.value());
    }
    db.commit(block_id, *builder, header, state, [&](BlockHeader &h) {
        h.receipts_root = db.receipts_root();
        h.state_root = db.state_root();
        h.withdrawals_root = db.withdrawals_root();
        h.transactions_root = db.transactions_root();
        h.gas_used = anc.receipts.empty() ? 0 : anc.receipts.back().gas_used;
        h.logs_bloom = compute_bloom(anc.receipts);
        h.ommers_hash = compute_ommers_hash(anc.ommers);
    });
}

EXPLICIT_MONAD_TRAITS(commit_block);

MONAD_NAMESPACE_END
