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

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/cli_tool_impl.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/trie.hpp>

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstring>
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
    std::string_view args[] = {"monad-mpt"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_EQ(retcode, 1);
    EXPECT_TRUE(cerr.str().starts_with("FATAL:"));
    {
        std::string out = cerr.str();
        std::transform(out.begin(), out.end(), out.begin(), ::tolower);
        EXPECT_NE(std::string::npos, out.find("options:"));
    }
}

TEST(cli_tool, help_prints_help)
{
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {"monad-mpt", "--help"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_EQ(retcode, 0);
    {
        std::string out = cout.str();
        std::transform(out.begin(), out.end(), out.begin(), ::tolower);
        EXPECT_NE(std::string::npos, out.find("options:"));
    }
}

TEST(cli_tool, create)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    auto const fd = mkstemp(temppath);
    if (-1 == fd) {
        abort();
    }
    ::close(fd);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    if (-1 == truncate(temppath, 6ULL * 1024 * 1024 * 1024)) {
        abort();
    }
    std::cout << "temp file being used: " << temppath << std::endl;
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
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
        constexpr unsigned default_num_cnv_chunks = 17;

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
        auto const untempfile = monad::make_scope_exit([&]() noexcept {
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
                "monad-mpt", "--storage", dbpath1, "--archive", temppath1};
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
                          (default_num_cnv_chunks + Config.chunks_max / 2) *
                                  MONAD_ASYNC_NAMESPACE::AsyncIO::
                                      MONAD_IO_BUFFERS_WRITE_SIZE +
                              24576)) {
                abort();
            }
            if (-1 == truncate(
                          dbpath2b,
                          (default_num_cnv_chunks + Config.chunks_max / 2) *
                                  MONAD_ASYNC_NAMESPACE::AsyncIO::
                                      MONAD_IO_BUFFERS_WRITE_SIZE +
                              24576)) {
                abort();
            }
            dbpath2.push_back(dbpath2a);
            dbpath2.push_back(dbpath2b);
        }
        else {
            if (-1 == truncate(
                          dbpath2a,
                          (default_num_cnv_chunks + Config.chunks_max) *
                                  MONAD_ASYNC_NAMESPACE::AsyncIO::
                                      MONAD_IO_BUFFERS_WRITE_SIZE +
                              24576)) {
                abort();
            }
            dbpath2.push_back(dbpath2a);
        }
        {
            std::cout << "restoring from file " << temppath1 << " to";
            for (auto const &i : dbpath2) {
                std::cout << " " << i;
            }
            std::cout << std::endl;
            std::stringstream cout;
            std::stringstream cerr;
            std::vector<std::string_view> args{
                "monad-mpt",
                "--chunk-capacity",
                "23",
                "--yes",
                "--restore",
                temppath1};
            for (auto const &i : dbpath2) {
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
                monad::mpt::UpdateAux const aux{testio};
                monad::mpt::Node::SharedPtr const root_ptr{read_node_blocking(
                    aux,
                    aux.metadata_ctx().get_latest_root_offset(),
                    aux.metadata_ctx().db_history_max_version(),
                    monad::mpt::timeline_id::primary)};
                monad::mpt::NodeCursor const root(root_ptr);

                for (auto const &key : this->state()->keys) {
                    auto const ret = monad::mpt::find_blocking(
                        aux,
                        root,
                        key.first,
                        aux.metadata_ctx().db_history_max_version(),
                        monad::mpt::timeline_id::primary);
                    EXPECT_EQ(ret.second, monad::mpt::find_result::success);
                }
                EXPECT_EQ(
                    this->state()
                        ->aux.metadata_ctx()
                        .db_history_min_valid_version(),
                    aux.metadata_ctx().db_history_min_valid_version());
                EXPECT_EQ(
                    this->state()->aux.metadata_ctx().db_history_max_version(),
                    aux.metadata_ctx().db_history_max_version());
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
            if (-1 == ftruncate(
                          fd,
                          (default_num_cnv_chunks + Config.chunks_max) *
                                  MONAD_ASYNC_NAMESPACE::AsyncIO::
                                      MONAD_IO_BUFFERS_WRITE_SIZE +
                              24576)) {
                abort();
            }
            ::close(fd);
            auto const untempfile2 = monad::make_scope_exit([&]() noexcept {
                unlink(temppath2);
                unlink(dbpath3);
            });
            {
                std::cout << "archiving to file: " << temppath2 << std::endl;
                std::stringstream cout;
                std::stringstream cerr;
                std::vector<std::string_view> args{
                    "monad-mpt", "--archive", temppath2};
                for (auto const &i : dbpath2) {
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
                    "monad-mpt",
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
                    monad::mpt::UpdateAux const aux{testio};
                    monad::mpt::Node::SharedPtr const root_ptr{
                        read_node_blocking(
                            aux,
                            aux.metadata_ctx().get_latest_root_offset(),
                            aux.metadata_ctx().db_history_max_version(),
                            monad::mpt::timeline_id::primary)};
                    monad::mpt::NodeCursor const root(root_ptr);

                    for (auto const &key : this->state()->keys) {
                        auto const ret = monad::mpt::find_blocking(
                            aux,
                            root,
                            key.first,
                            aux.metadata_ctx().db_history_max_version(),
                            monad::mpt::timeline_id::primary);
                        EXPECT_EQ(ret.second, monad::mpt::find_result::success);
                    }
                    EXPECT_EQ(
                        this->state()
                            ->aux.metadata_ctx()
                            .db_history_min_valid_version(),
                        aux.metadata_ctx().db_history_min_valid_version());
                    EXPECT_EQ(
                        this->state()
                            ->aux.metadata_ctx()
                            .db_history_max_version(),
                        aux.metadata_ctx().db_history_max_version());
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

// --upgrade on a pool created with --create and thus already on MONAD008.
// Must be idempotent: exit 0, print "DB is on version MONAD008".
TEST(cli_tool, upgrade_idempotent_on_current_pool)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    auto const fd = mkstemp(temppath);
    if (-1 == fd) {
        abort();
    }
    ::close(fd);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    if (-1 == truncate(temppath, 6ULL * 1024 * 1024 * 1024)) {
        abort();
    }

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--upgrade"};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(0, retcode);
        EXPECT_NE(
            std::string::npos, cout.str().find("DB is on version MONAD008"));
    }
}

// --upgrade combined with --create must be rejected at CLI parse time
// because cli_ops_group enforces require_option(0, 1).
TEST(cli_tool, upgrade_rejects_combined_mutation)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    auto const fd = mkstemp(temppath);
    if (-1 == fd) {
        abort();
    }
    ::close(fd);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    if (-1 == truncate(temppath, 6ULL * 1024 * 1024 * 1024)) {
        abort();
    }

    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {
        "monad-mpt", "--storage", temppath, "--upgrade", "--create"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_NE(0, retcode);
    EXPECT_TRUE(cerr.str().starts_with("FATAL:"));
}

// Full end-to-end: create a fresh MONAD008 pool, overwrite cnv chunk 0
// with a MONAD007 layout via the storage_pool's own chunk API (so the
// file offset is correct regardless of pool internal layout), then run
// monad-mpt --upgrade and verify the metadata is now MONAD008 and the
// history_length survived at its new offset.
TEST(cli_tool, upgrade_migrates_monad007_pool)
{
    using monad::mpt::detail::db_metadata;
    static constexpr size_t MONAD007_DB_METADATA_SIZE = 528512;
    static constexpr size_t MONAD007_LIST_TRIPLE_OFFSET = 528488;

    char temppath[] = "cli_tool_test_XXXXXX";
    auto const fd = mkstemp(temppath);
    if (-1 == fd) {
        abort();
    }
    ::close(fd);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    if (-1 == truncate(temppath, 6ULL * 1024 * 1024 * 1024)) {
        abort();
    }

    // Provision the file as a MONAD008 pool via --create.
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
    }

    // Overwrite cnv chunk 0 (both halves) with a MONAD007 layout. Open
    // the pool writable (allow_migration = false because the pool is
    // already MONAD008 — the ctor won't try to migrate), use the chunk
    // API to get the correct file offset for chunk 0 and the pool's
    // real chunk_count, then pwrite MONAD007 bytes over both halves.
    // Close the pool without writing metadata.
    //
    // The chunk_info[] array at MONAD007's offset MONAD007_DB_METADATA_SIZE
    // is zero-filled — zeros decode as INVALID_CHUNK_ID entries per
    // db_metadata convention, so relocation is a pure byte move and the
    // resulting MONAD008 pool passes UpdateAux::init's chunk_info_count
    // check.
    uint64_t const test_history_length = 9999;
    {
        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        // chunk_info_count stored on disk must equal io->chunk_count(),
        // which returns seq_chunks.size() only (see AsyncIO::chunk_count
        // and the new-pool init in DbMetadataContext ctor). The
        // chunk_info[] flexible array is sized to match.
        uint32_t const chunk_count = static_cast<uint32_t>(
            pool.chunks(MONAD_ASYNC_NAMESPACE::storage_pool::seq));
        auto &cnv_chunk =
            pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::cnv, 0);
        auto const [write_fd, base_offset] = cnv_chunk.write_fd(0);
        off_t const half_capacity = // NOLINT(misc-include-cleaner)
            static_cast<off_t>(cnv_chunk.capacity() / 2);

        std::vector<uint8_t> buf(
            MONAD007_DB_METADATA_SIZE +
                size_t(chunk_count) * sizeof(db_metadata::chunk_info_t),
            0);
        memcpy(
            buf.data(),
            db_metadata::PREVIOUS_MAGIC,
            db_metadata::MAGIC_STRING_LEN);
        uint64_t const bitfield =
            static_cast<uint64_t>(chunk_count) & 0xfffffULL;
        memcpy(buf.data() + 8, &bitfield, 8);
        uint32_t const high_bits_all_set = uint32_t(-1);
        uint32_t const cnv_len = 0;
        memcpy(buf.data() + 40, &high_bits_all_set, 4);
        memcpy(buf.data() + 44, &cnv_len, 4);
        memcpy(buf.data() + 524344, &test_history_length, 8);
        uint32_t const invalid = UINT32_MAX;
        for (int i = 0; i < 6; i++) {
            memcpy(
                buf.data() + MONAD007_LIST_TRIPLE_OFFSET + i * 4, &invalid, 4);
        }

        for (off_t copy_idx = 0; copy_idx < 2;
             copy_idx++) { // NOLINT(misc-include-cleaner)
            ssize_t const written = ::pwrite( // NOLINT(misc-include-cleaner)
                write_fd,
                buf.data(),
                buf.size(),
                off_t(base_offset) + copy_idx * half_capacity);
            ASSERT_EQ(ssize_t(buf.size()), written);
        }
        ASSERT_EQ(0, ::fsync(write_fd));
    }

    // Run --upgrade. Expect exit 0 and "Success." on stdout.
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--upgrade"};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(0, retcode) << "stderr: " << cerr.str();
        EXPECT_NE(std::string::npos, cout.str().find("Success."));
    }

    // Reopen read-only; magic must now be MONAD008 and history_length
    // must survive at its new offset.
    {
        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
        flags.open_read_only = true;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        monad::io::Ring ring;
        monad::io::Buffers rbuf = monad::io::make_buffers_for_read_only(
            ring,
            2,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
        MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, rbuf};
        monad::mpt::DbMetadataContext const ctx{io};
        auto const *const m = ctx.main();
        EXPECT_EQ(
            0,
            memcmp(
                m->magic, db_metadata::MAGIC, db_metadata::MAGIC_STRING_LEN));
        EXPECT_EQ(m->history_length, test_history_length);
    }
}

TEST(cli_tool, upgrade_requires_storage)
{
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {"monad-mpt", "--upgrade"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_NE(0, retcode);
    EXPECT_TRUE(cerr.str().starts_with("FATAL:"));
}
