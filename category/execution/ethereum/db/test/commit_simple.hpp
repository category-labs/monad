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
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/validate_block.hpp>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace test
{

    inline void commit_simple(
        ::monad::Db &db, StateDeltas const &deltas, Code const &code,
        bytes32_t const &block_id, BlockHeader const &header,
        std::vector<Receipt> const &receipts = {},
        std::vector<std::vector<CallFrame>> const &call_frames = {},
        std::vector<Address> const &senders = {},
        std::vector<Transaction> const &txns = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const &withdrawals =
            std::nullopt)
    {
        CommitBuilder builder(header.number);
        builder.add_state_deltas(deltas)
            .add_code(code)
            .add_receipts(receipts)
            .add_transactions(txns, senders)
            .add_call_frames(call_frames)
            .add_ommers(ommers);
        if (withdrawals.has_value()) {
            builder.add_withdrawals(withdrawals.value());
        }
        db.commit(
            block_id,
            builder,
            header,
            std::make_unique<StateDeltas>(deltas),
            [&](BlockHeader &h) {
                h.receipts_root = db.receipts_root();
                h.state_root = db.state_root();
                h.withdrawals_root = db.withdrawals_root();
                h.transactions_root = db.transactions_root();
                h.gas_used = receipts.empty() ? 0 : receipts.back().gas_used;
                h.logs_bloom = compute_bloom(receipts);
                h.ommers_hash = compute_ommers_hash(ommers);
            });
    }

} // namespace test

MONAD_NAMESPACE_END
