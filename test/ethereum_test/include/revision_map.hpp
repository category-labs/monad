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

#include <category/vm/evm/monad/revision.h>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>

#include <string>
#include <unordered_map>
#include <variant>

MONAD_TEST_NAMESPACE_BEGIN

inline std::unordered_map<
    std::string, std::variant<evmc_revision, monad_revision>> const
    revision_map = {
        {"Frontier", EVMC_FRONTIER},
        {"Homestead", EVMC_HOMESTEAD},
        {"EIP150", EVMC_TANGERINE_WHISTLE},
        {"TangerineWhistle", EVMC_TANGERINE_WHISTLE},
        {"EIP158", EVMC_SPURIOUS_DRAGON},
        {"SpuriousDragon", EVMC_SPURIOUS_DRAGON},
        {"Byzantium", EVMC_BYZANTIUM},
        {"Constantinople", EVMC_CONSTANTINOPLE},
        {"ConstantinopleFix", EVMC_PETERSBURG},
        {"Petersburg", EVMC_PETERSBURG},
        {"Istanbul", EVMC_ISTANBUL},
        {"Berlin", EVMC_BERLIN},
        {"London", EVMC_LONDON},
        {"Merge", EVMC_PARIS},
        {"Paris", EVMC_PARIS},
        {"Shanghai", EVMC_SHANGHAI},
        {"Cancun", EVMC_CANCUN},
        {"Prague", EVMC_PRAGUE},
        {"Osaka", EVMC_OSAKA},
        {"MONAD_ZERO", MONAD_ZERO},
        {"MONAD_ONE", MONAD_ONE},
        {"MONAD_TWO", MONAD_TWO},
        {"MONAD_THREE", MONAD_THREE},
        {"MONAD_FOUR", MONAD_FOUR},
        {"MONAD_FIVE", MONAD_FIVE},
        {"MONAD_SIX", MONAD_SIX},
        {"MONAD_SEVEN", MONAD_SEVEN},
        {"MONAD_EIGHT", MONAD_EIGHT},
        {"MONAD_NEXT", MONAD_NEXT}};

MONAD_TEST_NAMESPACE_END
