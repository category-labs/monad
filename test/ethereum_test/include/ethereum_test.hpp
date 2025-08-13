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

#include <category/execution/ethereum/db/trie_db.hpp>
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
    {"Cancun", EVMC_CANCUN},
    {"Prague", EVMC_PRAGUE}};

void load_state_from_json(nlohmann::json const &, State &);

MONAD_TEST_NAMESPACE_END
