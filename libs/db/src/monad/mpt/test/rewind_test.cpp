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

struct RewindTestFillOne
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{
              .chunks_to_fill = 1,
              .history_len = 65535,
              .updates_per_block = 1,
              .use_anonymous_inode = false}>
{
};

TEST_F(
    RewindTestFillOne,
    works_when_fast_writer_chunk_is_ahead_of_last_root_offset_chunk)
{
    // Test case to cover the case where fast writer is advanced to a newer
    // chunk than the latest root offset is at
    auto const path = this->state()->pool.devices()[0].current_path();
    auto &aux = this->state()->aux;
    auto &io = this->state()->io;
    auto const latest_root_offset = aux.get_latest_root_offset();
    std::cout << "DB is at " << path << ". Last root offset ["
              << latest_root_offset.id << ", " << latest_root_offset.offset
              << "]. " << std::endl;

    // advance fast writer head to the next chunk
    auto const fast_writer_offset = aux.node_writer_fast->sender().offset();
    auto const *ci = aux.db_metadata()->free_list_end();
    ASSERT_TRUE(ci != nullptr);
    auto const idx = ci->index(aux.db_metadata());
    aux.remove(idx);
    aux.append(monad::mpt::UpdateAuxImpl::chunk_list::fast, idx);
    monad::async::chunk_offset_t const new_fast_writer_offset{idx, 0};
    aux.advance_db_offsets_to(
        new_fast_writer_offset, aux.node_writer_slow->sender().offset());
    std::cout << "Advanced start of fast list offset on disk from ["
              << fast_writer_offset.id << ", " << fast_writer_offset.offset
              << "] to the beginning of a new chunk, id: " << idx << std::endl;

    std::cout << "Closing and reopening Db ...\n" << std::endl;
    aux.unset_io();

    // verifies set_io() succeeds
    aux.set_io(&io);
}
