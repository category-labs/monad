#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include "../cli_tool_impl.hpp"

#include <monad/async/config.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/io.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <filesystem>
#include <future>
#include <iostream>
#include <ostream>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include <stdlib.h>
#include <unistd.h>

using namespace monad::test;

TEST(cli_tool, no_args_prints_fatal_and_help)
{
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {"monad_mpt"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_EQ(retcode, 1);
    EXPECT_TRUE(cerr.str().starts_with("FATAL:"));
    EXPECT_NE(std::string::npos, cerr.str().find("Options:"));
}

TEST(cli_tool, help_prints_help)
{
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {"monad_mpt", "--help"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_EQ(retcode, 0);
    EXPECT_NE(std::string::npos, cout.str().find("Options:"));
}

TEST(cli_tool, create)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    auto const fd = mkstemp(temppath);
    if (-1 == fd) {
        abort();
    }
    ::close(fd);
    auto untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    if (-1 == truncate(temppath, 2ULL * 1024 * 1024 * 1024)) {
        abort();
    }
    std::cout << "temp file being used: " << temppath << std::endl;
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad_mpt", "--storage", temppath, "--create"};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(retcode, 0);
        EXPECT_NE(
            std::string::npos,
            cout.str().find(
                "1 chunks with capacity 256.00 Mb used 0.00 bytes"));
    }
}

struct config
{
    size_t chunks_to_fill;
    size_t chunks_max;
    bool interleave_multiple_sources{false};
};

template <config Config>
struct cli_tool_fixture
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{
              .chunks_to_fill = Config.chunks_to_fill,
              .chunks_max = Config.chunks_max,
              .use_anonymous_inode = false}>
{
    void run_test()
    {
        char temppath1[] = "cli_tool_test_XXXXXX";
        char dbpath2a[] = "cli_tool_test_XXXXXX";
        char dbpath2b[] = "cli_tool_test_XXXXXX";
        auto fd = mkstemp(temppath1);
        if (-1 == fd) {
            abort();
        }
        ::close(fd);
        fd = mkstemp(dbpath2a);
        if (-1 == fd) {
            abort();
        }
        ::close(fd);
        fd = mkstemp(dbpath2b);
        if (-1 == fd) {
            abort();
        }
        ::close(fd);
        auto untempfile = monad::make_scope_exit([&]() noexcept {
            unlink(temppath1);
            unlink(dbpath2a);
            unlink(dbpath2b);
        });
        auto const dbpath1 =
            this->state()->pool.devices().front().current_path().string();
        std::cout << "DB path: " << dbpath1 << std::endl;
        {
            std::cout << "archiving to file: " << temppath1 << std::endl;
            std::stringstream cout;
            std::stringstream cerr;
            std::string_view args[] = {
                "monad_mpt", "--storage", dbpath1, "--archive", temppath1};
            int const retcode = std::async(std::launch::async, [&] {
                                    return main_impl(cout, cerr, args);
                                }).get();
            ASSERT_EQ(retcode, 0);
            EXPECT_NE(
                std::string::npos,
                cout.str().find("Database has been archived to"));
        }
        std::vector<std::filesystem::path> dbpath2;
        if (Config.interleave_multiple_sources) {
            if (-1 == truncate(
                          dbpath2a,
                          (4 + Config.chunks_max / 2) *
                                  MONAD_ASYNC_NAMESPACE::AsyncIO::
                                      MONAD_IO_BUFFERS_WRITE_SIZE +
                              24576)) {
                abort();
            }
            if (-1 == truncate(
                          dbpath2b,
                          (4 + Config.chunks_max / 2) *
                                  MONAD_ASYNC_NAMESPACE::AsyncIO::
                                      MONAD_IO_BUFFERS_WRITE_SIZE +
                              24576)) {
                abort();
            }
            dbpath2.push_back(dbpath2a);
            dbpath2.push_back(dbpath2b);
        }
        else {
            if (-1 ==
                truncate(
                    dbpath2a,
                    (3 + Config.chunks_max) * MONAD_ASYNC_NAMESPACE::AsyncIO::
                                                  MONAD_IO_BUFFERS_WRITE_SIZE +
                        24576)) {
                abort();
            }
            dbpath2.push_back(dbpath2a);
        }
        {
            std::cout << "restoring from file " << temppath1 << " to";
            for (auto &i : dbpath2) {
                std::cout << " " << i;
            }
            std::cout << std::endl;
            std::stringstream cout;
            std::stringstream cerr;
            std::vector<std::string_view> args{
                "monad_mpt",
                "--chunk-capacity",
                "23",
                "--yes",
                "--restore",
                temppath1};
            for (auto &i : dbpath2) {
                args.push_back("--storage");
                args.push_back(i.native());
            }
            int const retcode = std::async(std::launch::async, [&] {
                                    return main_impl(cout, cerr, args);
                                }).get();
            std::cout << cerr.str() << std::endl;
            std::cout << cout.str() << std::endl;
            ASSERT_EQ(retcode, 0);
            EXPECT_NE(
                std::string::npos,
                cout.str().find("Database has been restored from"));
        }
        {
            std::cout << "checking restored file has correct contents"
                      << std::endl;

            std::async(std::launch::async, [&] {
                monad::async::storage_pool pool(dbpath2);
                monad::io::Ring testring;
                monad::io::Buffers testrwbuf =
                    monad::io::make_buffers_for_read_only(
                        testring,
                        1,
                        monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
                monad::async::AsyncIO testio(pool, testrwbuf);
                monad::mpt::UpdateAux<> const aux{&testio};
                monad::mpt::Node::UniquePtr root_ptr{read_node_blocking(
                    aux,
                    aux.get_latest_root_offset(),
                    aux.db_history_max_version())};
                monad::mpt::NodeCursor const root(*root_ptr);

                for (auto &key : this->state()->keys) {
                    auto ret = monad::mpt::find_blocking(
                        aux, root, key.first, aux.db_history_max_version());
                    EXPECT_EQ(ret.second, monad::mpt::find_result::success);
                }
                EXPECT_EQ(
                    this->state()->aux.db_history_min_valid_version(),
                    aux.db_history_min_valid_version());
                EXPECT_EQ(
                    this->state()->aux.db_history_max_version(),
                    aux.db_history_max_version());
            }).get();
        }
        if (Config.interleave_multiple_sources) {
            /* Also test archiving from a multiple source pool restoring into a
             single source pool, and see if the contents migrate properly.
             */
            char temppath2[] = "cli_tool_test_XXXXXX";
            char dbpath3[] = "cli_tool_test_XXXXXX";
            auto fd = mkstemp(temppath2);
            if (-1 == fd) {
                abort();
            }
            ::close(fd);
            fd = mkstemp(dbpath3);
            if (-1 == fd) {
                abort();
            }
            if (-1 ==
                ftruncate(
                    fd,
                    (3 + Config.chunks_max) * MONAD_ASYNC_NAMESPACE::AsyncIO::
                                                  MONAD_IO_BUFFERS_WRITE_SIZE +
                        24576)) {
                abort();
            }
            ::close(fd);
            auto untempfile2 = monad::make_scope_exit([&]() noexcept {
                unlink(temppath2);
                unlink(dbpath3);
            });
            {
                std::cout << "archiving to file: " << temppath2 << std::endl;
                std::stringstream cout;
                std::stringstream cerr;
                std::vector<std::string_view> args{
                    "monad_mpt", "--archive", temppath2};
                for (auto &i : dbpath2) {
                    args.push_back("--storage");
                    args.push_back(i.native());
                }
                int const retcode = std::async(std::launch::async, [&] {
                                        return main_impl(cout, cerr, args);
                                    }).get();
                ASSERT_EQ(retcode, 0);
                EXPECT_NE(
                    std::string::npos,
                    cout.str().find("Database has been archived to"));
            }
            {
                std::cout << "restoring from file " << temppath2 << " to "
                          << dbpath3 << std::endl;
                std::stringstream cout;
                std::stringstream cerr;
                std::string_view args[] = {
                    "monad_mpt",
                    "--storage",
                    dbpath3,
                    "--chunk-capacity",
                    "23",
                    "--yes",
                    "--restore",
                    temppath2};
                int const retcode = std::async(std::launch::async, [&] {
                                        return main_impl(cout, cerr, args);
                                    }).get();
                std::cout << cerr.str() << std::endl;
                std::cout << cout.str() << std::endl;
                ASSERT_EQ(retcode, 0);
                EXPECT_NE(
                    std::string::npos,
                    cout.str().find("Database has been restored from"));
            }
            {
                std::cout << "checking restored file has correct contents"
                          << std::endl;

                std::async(std::launch::async, [&] {
                    monad::async::storage_pool pool({{dbpath3}});
                    monad::io::Ring testring;
                    monad::io::Buffers testrwbuf =
                        monad::io::make_buffers_for_read_only(
                            testring,
                            1,
                            monad::async::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
                    monad::async::AsyncIO testio(pool, testrwbuf);
                    monad::mpt::UpdateAux<> const aux{&testio};
                    monad::mpt::Node::UniquePtr root_ptr{read_node_blocking(
                        aux,
                        aux.get_latest_root_offset(),
                        aux.db_history_max_version())};
                    monad::mpt::NodeCursor const root(*root_ptr);

                    for (auto &key : this->state()->keys) {
                        auto ret = monad::mpt::find_blocking(
                            aux, root, key.first, aux.db_history_max_version());
                        EXPECT_EQ(ret.second, monad::mpt::find_result::success);
                    }
                    EXPECT_EQ(
                        this->state()->aux.db_history_min_valid_version(),
                        aux.db_history_min_valid_version());
                    EXPECT_EQ(
                        this->state()->aux.db_history_max_version(),
                        aux.db_history_max_version());
                }).get();
            }
        }
    }
};

struct cli_tool_archives_restores
    : public cli_tool_fixture<config{.chunks_to_fill = 8, .chunks_max = 16}>
{
};

TEST_F(cli_tool_archives_restores, archives_restores)
{
    run_test();
}

/* There was a bug found whereby if the DB being archived used the lastmost
 chunk id for a given DB size, restoration into a same sized DB then
 failed because there should never be a chunk id larger than the chunks in
 the DB. As it should always be possible to backup and restore to
 identically sized DBs, this test ensures that this will remain so.
 */
struct cli_tool_one_chunk_too_many
    : public cli_tool_fixture<config{.chunks_to_fill = 4, .chunks_max = 6}>
{
};

TEST_F(cli_tool_one_chunk_too_many, one_chunk_too_many)
{
    run_test();
}

struct cli_tool_non_one_one_chunk_ids
    : public cli_tool_fixture<config{
          .chunks_to_fill = 4,
          .chunks_max = 6,
          .interleave_multiple_sources = true}>
{
};

TEST_F(cli_tool_non_one_one_chunk_ids, cli_tool_non_one_one_chunk_ids)
{
    run_test();
}
