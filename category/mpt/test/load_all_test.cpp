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

#include "test_fixtures_gtest.hpp"

#include <category/mpt/node.hpp>
#include <category/mpt/trie.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <iostream>
#include <ostream>

struct LoadAllTest
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = 2}>
{
};

TEST_F(LoadAllTest, works)
{
    monad::test::UpdateAux<void> aux{&state()->io};
    monad::test::StateMachineAlwaysMerkle sm;
    monad::mpt::Node::SharedPtr root{monad::mpt::read_node_blocking(
        state()->aux,
        aux.get_latest_root_offset(),
        aux.db_history_max_version())};
    auto nodes_loaded = monad::mpt::load_all(aux, sm, root);
    EXPECT_GE(nodes_loaded, state()->keys.size());
    std::cout << "   nodes_loaded = " << nodes_loaded << std::endl;
    nodes_loaded = monad::mpt::load_all(aux, sm, root);
    EXPECT_EQ(nodes_loaded, 0);
    std::cout << "   nodes_loaded = " << nodes_loaded << std::endl;
}
