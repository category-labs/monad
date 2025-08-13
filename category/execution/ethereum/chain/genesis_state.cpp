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
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>

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
        Address const addr = evmc::from_hex<Address>(item.key()).value();
        Account account{};
        account.balance =
            intx::from_string<uint256_t>(item.value()["wei_balance"]);
        deltas.emplace(addr, StateDelta{.account = {std::nullopt, account}});
    }
    db.commit(
        deltas,
        Code{},
        NULL_HASH_BLAKE3,
        genesis.header,
        std::vector<Receipt>{},
        std::vector<std::vector<CallFrame>>{},
        std::vector<Address>{},
        std::vector<Transaction>{},
        std::vector<BlockHeader>{},
        genesis.header.withdrawals_root == NULL_ROOT
            ? std::make_optional<std::vector<Withdrawal>>()
            : std::nullopt);
    db.finalize(0, NULL_HASH_BLAKE3);
}

MONAD_NAMESPACE_END
