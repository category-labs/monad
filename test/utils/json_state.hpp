// Copyright (C) 2025-26 Category Labs, Inc.
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

#include "test_state.hpp"

MONAD_TEST_NAMESPACE_BEGIN

struct JsonState
{
    monad::BlockHeader header;
    std::optional<std::vector<Withdrawal>> withdrawals;
    std::optional<nlohmann::json> init_state;
    std::optional<monad::bytes32_t> init_state_hash;

    TestStateRef make_test_state() const;
    std::vector<monad::Address> initial_accounts() const;
};

MONAD_TEST_NAMESPACE_END
