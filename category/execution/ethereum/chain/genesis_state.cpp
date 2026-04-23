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

#include <category/core/address.hpp>
#include <category/core/blake3.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/code.hpp>

#include <nlohmann/json.hpp>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

void load_genesis_state(GenesisState const &genesis, TrieDb &db)
{
    MONAD_ASSERT(genesis.alloc);
    MONAD_ASSERT(
        genesis.header.withdrawals_root == NULL_ROOT ||
        !genesis.header.withdrawals_root.has_value());

    StateDeltas deltas;
    Code code_map;

    auto const json = nlohmann::json::parse(genesis.alloc);
    for (auto const &item : json.items()) {
        Address const addr = from_hex<Address>(item.key()).value();
        auto const &value = item.value();

        Account account{};
        account.balance = intx::from_string<uint256_t>(value["wei_balance"]);

        if (auto const it = value.find("nonce"); it != value.end()) {
            account.nonce = std::stoull(it->get<std::string>(), nullptr, 0);
        }

        if (auto const it = value.find("code"); it != value.end()) {
            auto const code = it->get<std::string>();
            auto const code_bytes = from_hex(code);
            MONAD_ASSERT(code_bytes.has_value());

            account.code_hash = to_bytes(keccak256(*code_bytes));

            auto const intercode = vm::make_shared_intercode(*code_bytes);
            code_map.emplace(account.code_hash, intercode);
        }

        StateDelta state_delta{.account = {std::nullopt, account}};
        if (auto const it = value.find("storage"); it != value.end()) {
            for (auto const &storage_item : it->items()) {
                auto const slot =
                    from_hex<bytes32_t>(storage_item.key()).value();
                auto const slot_value =
                    from_hex<bytes32_t>(storage_item.value().get<std::string>())
                        .value();
                state_delta.storage.emplace(
                    slot, StorageDelta{bytes32_t{}, slot_value});
            }
        }

        deltas.emplace(addr, state_delta);
    }

    CommitBuilder builder(genesis.header.number);
    builder.add_state_deltas(deltas)
        .add_code(code_map)
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
