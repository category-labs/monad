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

#include <category/core/blake3.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/validate_block.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN

void load_genesis_state(GenesisState const &genesis, TrieDb &db)
{
    MONAD_ASSERT(genesis.alloc);
    MONAD_ASSERT(
        genesis.header.withdrawals_root == NULL_ROOT ||
        !genesis.header.withdrawals_root.has_value());
    StateDeltas deltas;
    auto const json = nlohmann::json::parse(genesis.alloc);
    for (auto const &item : json.items()) {
        Address const addr = from_hex<Address>(item.key()).value();
        Account account{};
        account.balance =
            intx::from_string<uint256_t>(item.value()["wei_balance"]);
        deltas.emplace(addr, StateDelta{.account = {std::nullopt, account}});
    }

    CommitBuilder builder(genesis.header.number);
    builder.add_state_deltas(deltas)
        .add_code(Code{})
        .add_receipts(std::vector<Receipt>{})
        .add_transactions(std::vector<Transaction>{}, std::vector<Address>{})
        .add_call_frames(std::vector<std::vector<CallFrame>>{})
        .add_ommers(std::vector<BlockHeader>{});
    if (genesis.header.withdrawals_root == NULL_ROOT) {
        builder.add_withdrawals({});
    }
    db.commit(
        NULL_HASH_BLAKE3, builder, genesis.header, deltas, [&](BlockHeader &h) {
            h.receipts_root = db.receipts_root();
            h.state_root = db.state_root();
            h.withdrawals_root = db.withdrawals_root();
            h.transactions_root = db.transactions_root();
            h.ommers_hash = compute_ommers_hash({});
        });

    db.finalize(0, NULL_HASH_BLAKE3);
}

MONAD_NAMESPACE_END
