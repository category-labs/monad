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
#include <category/vm/evm/revision.hpp>
#include <monad/test/config.hpp>

#include <string>
#include <unordered_map>
#include <variant>

MONAD_TEST_NAMESPACE_BEGIN

inline std::unordered_map<
    std::string, std::variant<EvmRevision, monad_revision>> const revision_map =
    {{"Berlin", EvmRevision::Berlin},
     {"London", EvmRevision::London},
     {"Merge", EvmRevision::Paris},
     {"Paris", EvmRevision::Paris},
     {"Shanghai", EvmRevision::Shanghai},
     {"Cancun", EvmRevision::Cancun},
     {"Prague", EvmRevision::Prague},
     {"Osaka", EvmRevision::Osaka},
     {"Amsterdam", EvmRevision::Amsterdam},
     {"BPO1", EvmRevision::Osaka},
     {"BPO2", EvmRevision::Osaka},
     {"OsakaToBPO1AtTime15k", EvmRevision::Osaka},
     {"BPO1ToBPO2AtTime15k", EvmRevision::Osaka},
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
     {"MONAD_TEN", MONAD_TEN},
     {"MONAD_NEXT", MONAD_NEXT}};

MONAD_TEST_NAMESPACE_END
