#include "test_fixtures_gtest.hpp"

#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

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
    monad::mpt::Node::UniquePtr root{monad::mpt::read_node_blocking(
        state()->aux,
        aux.get_latest_root_offset(),
        aux.db_history_max_version())};
    auto nodes_loaded = monad::mpt::load_all(aux, sm, *root);
    EXPECT_GE(nodes_loaded, state()->keys.size());
    std::cout << "   nodes_loaded = " << nodes_loaded << std::endl;
    nodes_loaded = monad::mpt::load_all(aux, sm, *root);
    EXPECT_EQ(nodes_loaded, 0);
    std::cout << "   nodes_loaded = " << nodes_loaded << std::endl;
}
