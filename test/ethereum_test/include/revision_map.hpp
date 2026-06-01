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
#include <category/vm/evm/revision.h>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>

#include <string>
#include <unordered_map>
#include <variant>

MONAD_TEST_NAMESPACE_BEGIN

inline std::unordered_map<
    std::string, std::variant<monad_eth_revision, monad_revision>> const
    revision_map = {
        {"Constantinople", MONAD_ETH_CONSTANTINOPLE},
        {"ConstantinopleFix", MONAD_ETH_PETERSBURG},
        {"Petersburg", MONAD_ETH_PETERSBURG},
        {"Istanbul", MONAD_ETH_ISTANBUL},
        {"Berlin", MONAD_ETH_BERLIN},
        {"London", MONAD_ETH_LONDON},
        {"Merge", MONAD_ETH_PARIS},
        {"Paris", MONAD_ETH_PARIS},
        {"Shanghai", MONAD_ETH_SHANGHAI},
        {"Cancun", MONAD_ETH_CANCUN},
        {"Prague", MONAD_ETH_PRAGUE},
        {"Osaka", MONAD_ETH_OSAKA},
        {"MONAD_ZERO", MONAD_ZERO},
        {"MONAD_ONE", MONAD_ONE},
        {"MONAD_TWO", MONAD_TWO},
        {"MONAD_THREE", MONAD_THREE},
        {"MONAD_FOUR", MONAD_FOUR},
        {"MONAD_FIVE", MONAD_FIVE},
        {"MONAD_SIX", MONAD_SIX},
        {"MONAD_SEVEN", MONAD_SEVEN},
        {"MONAD_EIGHT", MONAD_EIGHT},
        {"MONAD_NINE", MONAD_NINE},
        {"MONAD_NEXT", MONAD_NEXT}};

MONAD_TEST_NAMESPACE_END
