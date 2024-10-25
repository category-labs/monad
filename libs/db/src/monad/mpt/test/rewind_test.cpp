#include "test_fixtures_gtest.hpp"

#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <iostream>
#include <ostream>

struct RewindTest
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{
              .chunks_to_fill = 5,
              .history_len = 65535,
              .updates_per_block = 1,
              .use_anonymous_inode = false}>
{
};

TEST_F(RewindTest, works)
{
    auto const path = this->state()->pool.devices()[0].current_path();
    std::cout << "DB is at " << path << ". Closing DB ..." << std::endl;
    auto &aux = this->state()->aux;
    auto &io = this->state()->io;
    aux.unset_io();
    std::cout << "Reopening DB ..." << std::endl;
    aux.set_io(&io, 20000);
    std::cout << "Rewinding DB to 9990 ..." << std::endl;
    aux.rewind_to_version(9990);
    std::cout << "\nAfter rewind to 9990:\n";
    this->state()->print(std::cout);
    EXPECT_EQ(0, aux.db_history_min_valid_version());
    EXPECT_EQ(9990, aux.db_history_max_version());
    std::cout << "\nClosing DB ..." << std::endl;
    aux.unset_io();
    std::cout
        << "Reopening DB to check valid versions are what they should be ..."
        << std::endl;
    aux.set_io(&io);
    EXPECT_EQ(0, aux.db_history_min_valid_version());
    EXPECT_EQ(9990, aux.db_history_max_version());
    aux.unset_io();
    std::cout << "Setting max history to 9000 and reopening ..." << std::endl;
    aux.set_io(&io, 9000);
    EXPECT_EQ(991, aux.db_history_min_valid_version());
    EXPECT_EQ(9990, aux.db_history_max_version());
    aux.rewind_to_version(9900);
    EXPECT_EQ(991, aux.db_history_min_valid_version());
    EXPECT_EQ(9900, aux.db_history_max_version());
    aux.unset_io();
    aux.set_io(&io);
    EXPECT_EQ(991, aux.db_history_min_valid_version());
    EXPECT_EQ(9900, aux.db_history_max_version());
    aux.rewind_to_version(991);
    EXPECT_EQ(991, aux.db_history_min_valid_version());
    EXPECT_EQ(991, aux.db_history_max_version());
}
