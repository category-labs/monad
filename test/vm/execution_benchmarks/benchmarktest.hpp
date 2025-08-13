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

#include "state.hpp"
#include "statetest.hpp"
#include "test_state.hpp"

#include <evmc/evmc.hpp>
#include <span>
#include <vector>

namespace monad::test
{
    struct UnsupportedTestFeature : std::runtime_error
    {
        using runtime_error::runtime_error;
    };

    struct TestBlock
    {
        std::vector<evmone::state::Transaction> transactions;
    };

    struct BenchmarkTest
    {

        std::string name;

        std::vector<TestBlock> test_blocks;
        evmone::test::TestState pre_state;
    };

    std::vector<BenchmarkTest> load_benchmark_tests(std::istream &input);
} // namespace monad::test
