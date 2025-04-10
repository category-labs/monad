#pragma once

#include <monad/db/trie_db.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>

#include <nlohmann/json.hpp>

#include <string>
#include <unordered_map>

MONAD_NAMESPACE_BEGIN

class State;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

using db_t = monad::TrieDb;

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
    {"Shanghai", EVMC_SHANGHAI},
    {"Cancun", EVMC_CANCUN}};

void load_genesis_json_into_db(
    evmc_revision, nlohmann::json const &j_contents, db_t &tdb);
void load_state_from_json(nlohmann::json const &, State &);
void validate_post_state(nlohmann::json const &json, nlohmann::json const &db);

MONAD_TEST_NAMESPACE_END
