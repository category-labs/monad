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
#include <category/execution/ethereum/trace/prestate_tracer.hpp>

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
        std::vector<PreState>{},
        std::vector<StateDeltas>{},
        std::vector<Address>{},
        std::vector<Transaction>{},
        std::vector<BlockHeader>{},
        genesis.header.withdrawals_root == NULL_ROOT
            ? std::make_optional<std::vector<Withdrawal>>()
            : std::nullopt);
    db.finalize(0, NULL_HASH_BLAKE3);
}

MONAD_NAMESPACE_END
