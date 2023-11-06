#pragma once

#include <monad/db/in_memory_old_trie_db.hpp>
#include <monad/state2/state.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>

#include <nlohmann/json.hpp>

#include <string>
#include <unordered_map>

MONAD_TEST_NAMESPACE_BEGIN

using db_t = monad::db::InMemoryTrieDB;

inline std::unordered_map<std::string, evmc_revision> const revision_map = {
    {"Frontier", EVMC_FRONTIER},
    {"Homestead", EVMC_HOMESTEAD},
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
