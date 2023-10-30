#pragma once

#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/state2/state.hpp>
#include <monad/test/config.hpp>

#include <nlohmann/json.hpp>

MONAD_TEST_NAMESPACE_BEGIN

using db_t = monad::db::InMemoryTrieDB;

template <typename Traits>
using transaction_processor_t = TransactionProcessor<State, Traits>;

template <typename Traits>
using host_t = EvmcHost<Traits>;

inline std::unordered_map<std::string, evmc_revision> const revision_map = {
    {"Frontier", EVMC_FRONTIER},
    {"Homestead", EVMC_HOMESTEAD},
    // DAO not covered by Ethereum Tests
    {"EIP150", EVMC_TANGERINE_WHISTLE},
    {"EIP158", EVMC_SPURIOUS_DRAGON},
    {"Byzantium", EVMC_BYZANTIUM},
    {"ConstantinopleFix", EVMC_PETERSBURG},
    {"Istanbul", EVMC_ISTANBUL},
    {"Berlin", EVMC_BERLIN},
    {"London", EVMC_LONDON},
    {"Merge", EVMC_PARIS},
    {"Shanghai", EVMC_SHANGHAI}};

void load_state_from_json(nlohmann::json const &, State &);

MONAD_TEST_NAMESPACE_END
