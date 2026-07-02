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

#include "db_metadata_test_access.hpp"
#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/mpt/cli_tool_impl.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/trie.hpp>
#include <category/mpt/update.hpp>

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <future>
#include <iostream>
#include <memory>
#include <optional>
#include <ostream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
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
        // --state-machine defaults to ethereum on a fresh pool; confirm it
        // was stamped during pool init.
        EXPECT_NE(
            std::string::npos,
            cout.str().find("Stamped state-machine kind on primary timeline"));
    }
}

TEST(cli_tool, create_with_explicit_state_machine_flag)
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
        "monad-mpt",
        "--storage",
        temppath,
        "--create",
        "--state-machine",
        "ethereum"};
    int const retcode = main_impl(cout, cerr, args);
    ASSERT_EQ(retcode, 0);
    EXPECT_NE(
        std::string::npos,
        cout.str().find("Stamped state-machine kind on primary timeline"));
}

TEST(cli_tool, state_machine_unknown_kind_rejected)
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
        "monad-mpt",
        "--storage",
        temppath,
        "--create",
        "--state-machine",
        "nonsense"};
    int const retcode = main_impl(cout, cerr, args);
    EXPECT_NE(retcode, 0);
}

// 32 is a power of two but exceeds the per-ring cnv_chunks[] capacity
// (SIZE_ - 1 = 31), so the --root-offsets-chunk-count check must reject it
// before any pool is created.
TEST(cli_tool, root_offsets_chunk_count_over_capacity_rejected)
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
        "monad-mpt",
        "--storage",
        temppath,
        "--create",
        "--root-offsets-chunk-count",
        "32"};
    int const retcode = main_impl(cout, cerr, args);
    EXPECT_NE(retcode, 0);
}

namespace
{
    // Helper: open the pool RO and read back the persisted kind via
    // UpdateAux + DbMetadataContext public API. Lets CLI tests verify that
    // the bytes actually landed, not just that monad-mpt printed a success
    // line.
    monad::mpt::state_machine_kind
    read_kind(char const *const path, monad::mpt::timeline_id const tid)
    {
        monad::mpt::AsyncIOContext io_ctx{monad::mpt::ReadOnlyOnDiskDbConfig{
            .dbname_paths = {std::filesystem::path{path}}}};
        monad::mpt::UpdateAux const aux(io_ctx.io);
        return aux.metadata_ctx().get_state_machine_kind(tid);
    }

    bool read_secondary_active(char const *const path)
    {
        monad::mpt::AsyncIOContext io_ctx{monad::mpt::ReadOnlyOnDiskDbConfig{
            .dbname_paths = {std::filesystem::path{path}}}};
        monad::mpt::UpdateAux const aux(io_ctx.io);
        return aux.metadata_ctx().timeline_active(
            monad::mpt::timeline_id::secondary);
    }

    uint8_t read_primary_ring_idx(char const *const path)
    {
        monad::mpt::AsyncIOContext io_ctx{monad::mpt::ReadOnlyOnDiskDbConfig{
            .dbname_paths = {std::filesystem::path{path}}}};
        monad::mpt::UpdateAux const aux(io_ctx.io);
        return aux.metadata_ctx().primary_ring_idx();
    }

    // Provision a temp pool file. Caller owns the unlink scope.
    void make_temp_pool(char *const temppath)
    {
        auto const fd = ::mkstemp(temppath);
        ASSERT_NE(fd, -1);
        ::close(fd);
        ASSERT_EQ(0, ::truncate(temppath, 6ULL * 1024 * 1024 * 1024));
    }

    // Provision `temppath` (an empty temp file) as a MONAD008 pool via
    // --create, then overwrite cnv chunk 0 (both metadata copies) with a
    // MONAD007 (pre-dual-timeline) layout whose primary root_offsets ring
    // lists `primary_chunk_ids`. Mirrors a pool created before dual-timeline
    // support and left ready for a --upgrade. cnv chunk 0 is the metadata
    // chunk; ring data chunks are ids >= 1.
    void provision_monad007_pool(
        char const *const temppath,
        std::vector<uint32_t> const &primary_chunk_ids,
        uint64_t const history_length)
    {
        using monad::mpt::detail::db_metadata;
        static constexpr size_t MONAD007_DB_METADATA_SIZE = 528512;
        static constexpr size_t MONAD007_LIST_TRIPLE_OFFSET = 528488;
        static constexpr size_t MONAD007_HISTORY_LENGTH_OFFSET = 524344;
        // root_offsets.storage_ header lives at byte 40; cnv_chunks_len at 44;
        // cnv_chunks[k] = {high_bits_all_set@(48+8k), cnv_chunk_id@(52+8k)}.
        static constexpr size_t STORAGE_HIGH_BITS_OFFSET = 40;
        static constexpr size_t STORAGE_CNV_LEN_OFFSET = 44;
        static constexpr size_t STORAGE_CNV_CHUNKS_OFFSET = 48;

        {
            std::stringstream cout;
            std::stringstream cerr;
            std::string_view create_args[] = {
                "monad-mpt", "--storage", temppath, "--create"};
            ASSERT_EQ(0, main_impl(cout, cerr, create_args)) << cerr.str();
        }

        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        auto const chunk_count = static_cast<uint32_t>(
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
        auto const cnv_len = static_cast<uint32_t>(primary_chunk_ids.size());
        memcpy(buf.data() + STORAGE_HIGH_BITS_OFFSET, &high_bits_all_set, 4);
        memcpy(buf.data() + STORAGE_CNV_LEN_OFFSET, &cnv_len, 4);
        for (size_t k = 0; k < primary_chunk_ids.size(); k++) {
            memcpy(
                buf.data() + STORAGE_CNV_CHUNKS_OFFSET + k * 8,
                &high_bits_all_set,
                4);
            memcpy(
                buf.data() + STORAGE_CNV_CHUNKS_OFFSET + k * 8 + 4,
                &primary_chunk_ids[k],
                4);
        }
        memcpy(buf.data() + MONAD007_HISTORY_LENGTH_OFFSET, &history_length, 8);
        uint32_t const invalid = db_metadata::NULL_CHUNK;
        for (int i = 0; i < 6; i++) {
            memcpy(
                buf.data() + MONAD007_LIST_TRIPLE_OFFSET + i * 4, &invalid, 4);
        }

        for (off_t copy_idx = 0; copy_idx < 2; copy_idx++) {
            ssize_t const written = ::pwrite( // NOLINT(misc-include-cleaner)
                write_fd,
                buf.data(),
                buf.size(),
                off_t(base_offset) + copy_idx * half_capacity);
            ASSERT_EQ(ssize_t(buf.size()), written);
        }
        ASSERT_EQ(0, ::fsync(write_fd));
    }

    monad::mpt::Node::SharedPtr upsert_one(
        monad::mpt::Db &target, monad::byte_string const &key,
        monad::byte_string const &value, monad::mpt::Node::SharedPtr root)
    {
        monad::mpt::UpdateList ul;
        auto u = monad::mpt::make_update(
            monad::mpt::NibblesView{key}, monad::byte_string_view{value});
        ul.push_front(u);
        return target.upsert(std::move(root), std::move(ul), 0);
    }
}

TEST(cli_tool, activate_secondary_stamps_secondary_kind)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view create_args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, create_args));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt",
            "--storage",
            temppath,
            "--activate-secondary",
            "--state-machine",
            "ethereum"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
        EXPECT_NE(
            std::string::npos,
            cout.str().find(
                "Activated secondary timeline; stamped state-machine"));
    }

    EXPECT_TRUE(read_secondary_active(temppath));
    EXPECT_EQ(
        read_kind(temppath, monad::mpt::timeline_id::primary),
        monad::mpt::state_machine_kind::ethereum);
    EXPECT_EQ(
        read_kind(temppath, monad::mpt::timeline_id::secondary),
        monad::mpt::state_machine_kind::ethereum);
}

TEST(cli_tool, activate_secondary_defaults_to_ethereum_when_flag_omitted)
{
    // Pins the design choice that --state-machine defaults to ethereum on
    // --activate-secondary (matching the --create default), so existing
    // operator scripts work unmodified. If you change this default, this
    // test should fail and force a deliberate choice.
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view create_args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, create_args));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--activate-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
    }
    EXPECT_EQ(
        read_kind(temppath, monad::mpt::timeline_id::secondary),
        monad::mpt::state_machine_kind::ethereum);
}

TEST(cli_tool, deactivate_secondary_clears_active_flag)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view create_args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, create_args));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--activate-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
    }
    ASSERT_TRUE(read_secondary_active(temppath));

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--deactivate-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
        EXPECT_NE(
            std::string::npos,
            cout.str().find("Deactivated secondary timeline"));
    }

    EXPECT_FALSE(read_secondary_active(temppath));
}

TEST(cli_tool, promote_secondary_flips_primary_ring_idx)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view create_args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, create_args));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--activate-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
    }
    ASSERT_EQ(0u, read_primary_ring_idx(temppath));

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--promote-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
        EXPECT_NE(
            std::string::npos,
            cout.str().find("Promoted secondary timeline to primary"));
    }

    EXPECT_EQ(1u, read_primary_ring_idx(temppath));
}

TEST(cli_tool, activate_secondary_on_already_active_is_rejected)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view create_args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, create_args));
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--activate-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
    }
    // Second activate must refuse without mutating state.
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {
        "monad-mpt", "--storage", temppath, "--activate-secondary"};
    EXPECT_NE(0, main_impl(cout, cerr, args));
    EXPECT_NE(std::string::npos, cerr.str().find("already active"));
}

TEST(cli_tool, deactivate_secondary_on_inactive_is_rejected)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view create_args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, create_args));
    }
    std::stringstream cout;
    std::stringstream cerr;
    std::string_view args[] = {
        "monad-mpt", "--storage", temppath, "--deactivate-secondary"};
    EXPECT_NE(0, main_impl(cout, cerr, args));
    EXPECT_NE(std::string::npos, cerr.str().find("not active"));
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

struct cli_tool_restore_preserves_kind
    : public cli_tool_fixture<config{.chunks_to_fill = 8, .chunks_max = 16}>
{
};

// Regression: do_restore_database() once copied only
// root_offsets_state.auto_expire_version_ out of the source metadata, leaving
// state_machine_kind_ at the destination's freshly-initialised ethereum
// default — silently dropping a non-ethereum source DB's kind on --restore.
// ethereum (== 0) is the only registered kind, so comparing reads back can't
// tell a copied byte from a zero-initialised one; stamp a synthetic non-zero
// kind to make the archive/restore round-trip observable.
TEST_F(cli_tool_restore_preserves_kind, restore_preserves_state_machine_kind)
{
    constexpr auto synthetic_kind =
        static_cast<monad::mpt::state_machine_kind>(uint8_t{3});

    auto const dbpath1 =
        this->state()->pool.devices().front().current_path().string();
    this->state()->aux.metadata_ctx().set_state_machine_kind(
        monad::mpt::timeline_id::primary, synthetic_kind);

    constexpr unsigned default_num_cnv_chunks = 17;
    char archivepath[] = "cli_tool_test_XXXXXX";
    char dbpath2[] = "cli_tool_test_XXXXXX";
    {
        auto const fd = mkstemp(archivepath);
        ASSERT_NE(fd, -1);
        ::close(fd);
    }
    {
        auto const fd = mkstemp(dbpath2);
        ASSERT_NE(fd, -1);
        ::close(fd);
    }
    ASSERT_EQ(
        0,
        truncate(
            dbpath2,
            (default_num_cnv_chunks +
             16) * MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE +
                24576));
    auto const cleanup = monad::make_scope_exit([&]() noexcept {
        unlink(archivepath);
        unlink(dbpath2);
    });

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt",
            "--storage",
            dbpath1.c_str(),
            "--archive",
            archivepath};
        int const retcode = std::async(std::launch::async, [&] {
                                return main_impl(cout, cerr, args);
                            }).get();
        ASSERT_EQ(retcode, 0) << cerr.str();
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt",
            "--chunk-capacity",
            "23",
            "--yes",
            "--restore",
            archivepath,
            "--storage",
            dbpath2};
        int const retcode = std::async(std::launch::async, [&] {
                                return main_impl(cout, cerr, args);
                            }).get();
        ASSERT_EQ(retcode, 0) << cerr.str();
        EXPECT_NE(
            std::string::npos,
            cout.str().find("Database has been restored from"));
    }

    // read_kind opens its own AsyncIO; the fixture already holds one on this
    // thread, so run it on a fresh thread (one AsyncIO per thread).
    auto const restored_kind =
        std::async(std::launch::async, [&] {
            return read_kind(dbpath2, monad::mpt::timeline_id::primary);
        }).get();
    EXPECT_EQ(restored_kind, synthetic_kind);
}

// Round-trips a Db whose secondary timeline is active and holds a key
// distinct from the primary. The archive must capture both rings' cnv
// chunks; otherwise the restored secondary's root_offsets come up
// zeroed and the find below fails.
TEST(cli_tool, archives_restores_with_secondary_active)
{
    using namespace monad::mpt;
    using monad::literals::operator""_bytes;

    auto const src_dbname = create_temp_file(8);
    auto const dst_dbname = create_temp_file(8);
    char arc_path[] = "cli_tool_test_XXXXXX";
    int const arc_fd = ::mkstemp(arc_path);
    ASSERT_NE(arc_fd, -1);
    ::close(arc_fd);
    auto const unfiles = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(src_dbname);
        std::filesystem::remove(dst_dbname);
        ::unlink(arc_path);
    });

    auto const k_primary = 0xaabbccdd_bytes;
    auto const v_primary = 0x11223344_bytes;
    auto const k_secondary = 0xeeff0011_bytes;
    auto const v_secondary = 0x55667788_bytes;

    {
        OnDiskDbConfig const config{
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {src_dbname},
            .fixed_history_length = MPT_TEST_HISTORY_LENGTH};
        Db db{std::make_unique<StateMachineAlwaysMerkle>(), config};

        Node::SharedPtr const primary_root =
            upsert_one(db, k_primary, v_primary, nullptr);
        ASSERT_NE(primary_root, nullptr);

        {
            Db secondary_db = db.activate_secondary_timeline(
                std::make_unique<StateMachineAlwaysMerkle>());
            Node::SharedPtr const secondary_root =
                upsert_one(secondary_db, k_secondary, v_secondary, nullptr);
            ASSERT_NE(secondary_root, nullptr);
        }
    }

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt",
            "--storage",
            src_dbname.c_str(),
            "--archive",
            arc_path};
        int const retcode = std::async(std::launch::async, [&] {
                                return main_impl(cout, cerr, args);
                            }).get();
        ASSERT_EQ(retcode, 0)
            << "stderr: " << cerr.str() << "\nstdout: " << cout.str();
        EXPECT_NE(
            std::string::npos,
            cout.str().find("Database has been archived to"));
    }

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt",
            "--storage",
            dst_dbname.c_str(),
            "--root-offsets-chunk-count",
            "2",
            "--yes",
            "--restore",
            arc_path};
        int const retcode = std::async(std::launch::async, [&] {
                                return main_impl(cout, cerr, args);
                            }).get();
        ASSERT_EQ(retcode, 0)
            << "stderr: " << cerr.str() << "\nstdout: " << cout.str();
        EXPECT_NE(
            std::string::npos,
            cout.str().find("Database has been restored from"));
    }

    EXPECT_TRUE(read_secondary_active(dst_dbname.c_str()));
    EXPECT_EQ(0u, read_primary_ring_idx(dst_dbname.c_str()));

    {
        OnDiskDbConfig const config{
            .append = true,
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dst_dbname},
            .fixed_history_length = MPT_TEST_HISTORY_LENGTH};
        Db db{std::make_unique<StateMachineAlwaysMerkle>(), config};
        ASSERT_TRUE(db.timeline_active(timeline_id::secondary));

        Node::SharedPtr const primary_root = db.load_root_for_version(0);
        ASSERT_NE(primary_root, nullptr);
        auto const pres =
            db.find(NodeCursor{primary_root}, NibblesView{k_primary}, 0);
        ASSERT_TRUE(pres.has_value());
        EXPECT_EQ(monad::byte_string{pres.value().node->value()}, v_primary);

        auto secondary_db_opt = db.open_secondary_timeline(
            std::make_unique<StateMachineAlwaysMerkle>());
        ASSERT_TRUE(secondary_db_opt.has_value());
        Node::SharedPtr const secondary_root =
            secondary_db_opt->load_root_for_version(0);
        ASSERT_NE(secondary_root, nullptr);
        auto const sres = secondary_db_opt->find(
            NodeCursor{secondary_root}, NibblesView{k_secondary}, 0);
        ASSERT_TRUE(sres.has_value());
        EXPECT_EQ(monad::byte_string{sres.value().node->value()}, v_secondary);
    }
}

// Round-trips a Db after promote_secondary_to_primary +
// deactivate_secondary_timeline, where primary_ring_idx == 1 and the
// live data sits on the physical ring named by secondary_timeline (now
// playing the primary role). The archive must dispatch by role, not by
// physical ring slot; walking m->root_offsets unconditionally would
// archive the stale, deactivated ring and lose the only live data.
TEST(cli_tool, archives_restores_after_promote_and_deactivate)
{
    using namespace monad::mpt;
    using monad::literals::operator""_bytes;

    auto const src_dbname = create_temp_file(8);
    auto const dst_dbname = create_temp_file(8);
    char arc_path[] = "cli_tool_test_XXXXXX";
    int const arc_fd = ::mkstemp(arc_path);
    ASSERT_NE(arc_fd, -1);
    ::close(arc_fd);
    auto const unfiles = monad::make_scope_exit([&]() noexcept {
        std::filesystem::remove(src_dbname);
        std::filesystem::remove(dst_dbname);
        ::unlink(arc_path);
    });

    auto const k_kept = 0xeeff0011_bytes;
    auto const v_kept = 0x55667788_bytes;
    auto const k_discarded = 0xaabbccdd_bytes;
    auto const v_discarded = 0x11223344_bytes;

    OnDiskDbConfig const config{
        .compaction = true,
        .sq_thread_cpu = std::nullopt,
        .dbname_paths = {src_dbname},
        .fixed_history_length = MPT_TEST_HISTORY_LENGTH};

    {
        Db db{std::make_unique<StateMachineAlwaysMerkle>(), config};

        Node::SharedPtr const primary_root =
            upsert_one(db, k_discarded, v_discarded, nullptr);
        ASSERT_NE(primary_root, nullptr);

        {
            Db secondary_db = db.activate_secondary_timeline(
                std::make_unique<StateMachineAlwaysMerkle>());
            Node::SharedPtr const secondary_root =
                upsert_one(secondary_db, k_kept, v_kept, nullptr);
            ASSERT_NE(secondary_root, nullptr);
        }

        db.promote_secondary_to_primary();
    }

    OnDiskDbConfig reopen_config = config;
    reopen_config.append = true;
    {
        Db db{std::make_unique<StateMachineAlwaysMerkle>(), reopen_config};
        db.deactivate_secondary_timeline();
    }

    ASSERT_EQ(1u, read_primary_ring_idx(src_dbname.c_str()));
    ASSERT_FALSE(read_secondary_active(src_dbname.c_str()));

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt",
            "--storage",
            src_dbname.c_str(),
            "--archive",
            arc_path};
        int const retcode = std::async(std::launch::async, [&] {
                                return main_impl(cout, cerr, args);
                            }).get();
        ASSERT_EQ(retcode, 0)
            << "stderr: " << cerr.str() << "\nstdout: " << cout.str();
    }

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt",
            "--storage",
            dst_dbname.c_str(),
            "--root-offsets-chunk-count",
            "2",
            "--yes",
            "--restore",
            arc_path};
        int const retcode = std::async(std::launch::async, [&] {
                                return main_impl(cout, cerr, args);
                            }).get();
        ASSERT_EQ(retcode, 0)
            << "stderr: " << cerr.str() << "\nstdout: " << cout.str();
    }

    EXPECT_EQ(1u, read_primary_ring_idx(dst_dbname.c_str()));
    EXPECT_FALSE(read_secondary_active(dst_dbname.c_str()));

    {
        OnDiskDbConfig const restored_config{
            .append = true,
            .compaction = true,
            .sq_thread_cpu = std::nullopt,
            .dbname_paths = {dst_dbname},
            .fixed_history_length = MPT_TEST_HISTORY_LENGTH};
        Db const db{
            std::make_unique<StateMachineAlwaysMerkle>(), restored_config};
        EXPECT_FALSE(db.timeline_active(timeline_id::secondary));

        Node::SharedPtr const root = db.load_root_for_version(0);
        ASSERT_NE(root, nullptr);
        auto const res = db.find(NodeCursor{root}, NibblesView{k_kept}, 0);
        ASSERT_TRUE(res.has_value());
        EXPECT_EQ(monad::byte_string{res.value().node->value()}, v_kept);
    }
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
        uint32_t const invalid = db_metadata::NULL_CHUNK;
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

// A pool migrated MONAD007 -> MONAD008 must have its (empty) secondary ring
// initialised with the NULL_CHUNK sentinel, not zero. A zeroed cnv_chunks[]
// slot decodes as cnv chunk id 0 — the db_metadata chunk — which a later
// activate_secondary would map and then 0xff-fill, destroying the metadata.
TEST(cli_tool, upgrade_monad007_secondary_ring_uses_null_chunk_sentinel)
{
    using monad::mpt::detail::db_metadata;
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    provision_monad007_pool(temppath, {1, 2}, /*history_length=*/9999);
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--upgrade"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }

    monad::mpt::AsyncIOContext io_ctx{monad::mpt::ReadOnlyOnDiskDbConfig{
        .dbname_paths = {std::filesystem::path{temppath}}}};
    monad::mpt::DbMetadataContext const ctx{io_ctx.io};
    auto const *const m = ctx.main();
    ASSERT_EQ(
        0, memcmp(m->magic, db_metadata::MAGIC, db_metadata::MAGIC_STRING_LEN));

    auto const &sstore =
        monad::mpt::test::DbMetadataTestAccess::storage(m->secondary_timeline);
    EXPECT_EQ(sstore.cnv_chunks_len, 0u);
    for (size_t k = 0; k < db_metadata::root_offsets_ring_t::SIZE_ - 1; k++) {
        EXPECT_EQ(sstore.cnv_chunks[k].cnv_chunk_id, db_metadata::NULL_CHUNK)
            << "secondary cnv_chunks[" << k
            << "] must be the NULL_CHUNK sentinel, not a valid chunk id "
               "(0 == the db_metadata chunk)";
    }
}

// End-to-end regression for the metadata-wipe incident: a MONAD007 pool that
// is --upgrade'd and then has its secondary timeline activated must keep its
// metadata intact (magic valid) and bind the secondary to a real ring chunk.
// Before the fix, activate mapped the secondary ring onto cnv chunk 0 and
// 0xff-filled it, corrupting the magic so every subsequent open aborted.
//
// Activate is driven at the metadata level (activate_secondary_header) rather
// than via the CLI: the full UpdateAux::init that `monad-mpt
// --activate-secondary` runs requires a populated fast/slow chunk list that
// this synthetic MONAD007 pool doesn't have, whereas the wipe bug lives
// entirely in the metadata-level activate body.
TEST(cli_tool, activate_secondary_on_migrated_pool_preserves_metadata)
{
    using monad::mpt::detail::db_metadata;
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });

    provision_monad007_pool(temppath, {1, 2}, /*history_length=*/9999);
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--upgrade"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }

    {
        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        monad::io::Ring ring1;
        monad::io::Ring ring2;
        monad::io::Buffers buffers =
            monad::io::make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                2,
                4,
                MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
        MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, buffers};
        monad::mpt::DbMetadataContext ctx{io};

        ASSERT_FALSE(ctx.timeline_active(monad::mpt::timeline_id::secondary));
        ctx.activate_secondary_header();

        auto const *const m = ctx.main();
        ASSERT_EQ(
            0,
            memcmp(m->magic, db_metadata::MAGIC, db_metadata::MAGIC_STRING_LEN))
            << "activate destroyed the metadata magic (the wipe bug)";
        EXPECT_TRUE(ctx.timeline_active(monad::mpt::timeline_id::secondary));

        auto const &sstore = monad::mpt::test::DbMetadataTestAccess::storage(
            m->secondary_timeline);
        EXPECT_EQ(sstore.cnv_chunks_len, 1u);
        EXPECT_NE(sstore.cnv_chunks[0].cnv_chunk_id, 0u);
        EXPECT_NE(sstore.cnv_chunks[0].cnv_chunk_id, db_metadata::NULL_CHUNK);
    }

    monad::mpt::AsyncIOContext io_ctx{monad::mpt::ReadOnlyOnDiskDbConfig{
        .dbname_paths = {std::filesystem::path{temppath}}}};
    monad::mpt::DbMetadataContext const ctx{io_ctx.io};
    EXPECT_EQ(
        0,
        memcmp(
            ctx.main()->magic,
            db_metadata::MAGIC,
            db_metadata::MAGIC_STRING_LEN));
    EXPECT_TRUE(ctx.timeline_active(monad::mpt::timeline_id::secondary));
}

// Guard: a root-offsets ring must never reference cnv chunk 0 (it holds
// db_metadata). Corrupt a fresh pool's primary ring to point slot 0 at chunk
// 0 and confirm the next open aborts, instead of mapping (and a later op
// 0xff-wiping) the metadata chunk.
TEST(cli_tool, ring_referencing_db_metadata_chunk_aborts)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }

    // Point primary root_offsets ring slot 0 at cnv chunk 0 on both metadata
    // copies. cnv_chunks[0].cnv_chunk_id sits at byte 52 of db_metadata.
    {
        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        auto &cnv_chunk =
            pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::cnv, 0);
        auto const [write_fd, base_offset] = cnv_chunk.write_fd(0);
        auto const half_capacity = static_cast<off_t>(cnv_chunk.capacity() / 2);
        uint32_t const chunk0_id = 0;
        for (off_t copy_idx = 0; copy_idx < 2; copy_idx++) {
            ASSERT_EQ(
                4,
                ::pwrite(
                    write_fd,
                    &chunk0_id,
                    4,
                    off_t(base_offset) + copy_idx * half_capacity + 52));
        }
        ASSERT_EQ(0, ::fsync(write_fd));
    }

    monad::mpt::AsyncIOContext io_ctx{monad::mpt::ReadOnlyOnDiskDbConfig{
        .dbname_paths = {std::filesystem::path{temppath}}}};
    ASSERT_DEATH(
        { monad::mpt::DbMetadataContext const ctx{io_ctx.io}; },
        "db_metadata chunk");
}

// monad-mpt --repair path: a pool whose inactive secondary ring was left with
// a zeroed cnv_chunks[] (the pre-fix migration artifact) is normalised back to
// the NULL_CHUNK sentinel, and repair is idempotent.
TEST(cli_tool, repair_normalizes_zeroed_secondary_ring)
{
    using monad::mpt::detail::db_metadata;
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }

    // Simulate the buggy migration artifact: zero the inactive secondary
    // ring's cnv_chunks[0].cnv_chunk_id (byte 460 = secondary_timeline@432 +
    // storage_ cnv_chunks[0].cnv_chunk_id@28) on both metadata copies.
    static constexpr off_t SECONDARY_CNV_CHUNK0_ID_OFFSET = 432 + 28;
    {
        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        auto &cnv_chunk =
            pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::cnv, 0);
        auto const [write_fd, base_offset] = cnv_chunk.write_fd(0);
        auto const half_capacity = static_cast<off_t>(cnv_chunk.capacity() / 2);
        uint32_t const zero_id = 0;
        for (off_t copy_idx = 0; copy_idx < 2; copy_idx++) {
            ASSERT_EQ(
                4,
                ::pwrite(
                    write_fd,
                    &zero_id,
                    4,
                    off_t(base_offset) + copy_idx * half_capacity +
                        SECONDARY_CNV_CHUNK0_ID_OFFSET));
        }
        ASSERT_EQ(0, ::fsync(write_fd));
    }

    std::vector<std::filesystem::path> paths{temppath};
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        std::span{paths},
        MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
        flags};
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers buffers =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, buffers};
    monad::mpt::DbMetadataContext ctx{io};

    // Sanity: the artifact is present.
    ASSERT_EQ(
        monad::mpt::test::DbMetadataTestAccess::storage(
            ctx.main()->secondary_timeline)
            .cnv_chunks[0]
            .cnv_chunk_id,
        0u);

    EXPECT_TRUE(ctx.repair_inactive_secondary_ring());

    auto const &sstore = monad::mpt::test::DbMetadataTestAccess::storage(
        ctx.main()->secondary_timeline);
    EXPECT_EQ(sstore.cnv_chunks_len, 0u);
    for (auto const &slot : sstore.cnv_chunks) {
        EXPECT_EQ(slot.cnv_chunk_id, db_metadata::NULL_CHUNK);
    }
    // Idempotent: nothing left to repair.
    EXPECT_FALSE(ctx.repair_inactive_secondary_ring());
}

// End-to-end CLI wiring for --repair: on a healthy (fresh) pool it parses,
// opens writable, and reports nothing to do.
TEST(cli_tool, repair_cli_noop_on_healthy_pool)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--repair"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
        EXPECT_NE(std::string::npos, cout.str().find("No repair needed"));
    }
}

// --repair must refuse to touch an ACTIVE secondary (whose ring holds real
// data) — the guard against repair itself destroying live mappings.
TEST(cli_tool, repair_refuses_active_secondary)
{
    using monad::mpt::detail::db_metadata;
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }

    std::vector<std::filesystem::path> paths{temppath};
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
    MONAD_ASYNC_NAMESPACE::storage_pool pool{
        std::span{paths},
        MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
        flags};
    monad::io::Ring ring1;
    monad::io::Ring ring2;
    monad::io::Buffers buffers =
        monad::io::make_buffers_for_segregated_read_write(
            ring1,
            ring2,
            2,
            4,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);
    MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, buffers};
    monad::mpt::DbMetadataContext ctx{io};

    // Activate the secondary so its ring holds real chunk ids.
    ctx.activate_secondary_header();
    ASSERT_TRUE(ctx.timeline_active(monad::mpt::timeline_id::secondary));
    auto const real_chunk = monad::mpt::test::DbMetadataTestAccess::storage(
                                ctx.main()->secondary_timeline)
                                .cnv_chunks[0]
                                .cnv_chunk_id;
    ASSERT_NE(real_chunk, 0u);
    ASSERT_NE(real_chunk, db_metadata::NULL_CHUNK);

    // Repair must be a no-op on an active secondary and must not disturb it.
    EXPECT_FALSE(ctx.secondary_ring_needs_repair());
    EXPECT_FALSE(ctx.repair_inactive_secondary_ring());
    EXPECT_EQ(
        monad::mpt::test::DbMetadataTestAccess::storage(
            ctx.main()->secondary_timeline)
            .cnv_chunks[0]
            .cnv_chunk_id,
        real_chunk);
}

// CLI --repair on a pool with an ACTIVE secondary is a precondition violation:
// it must report the refusal on stderr and exit non-zero (like the other
// secondary-lifecycle ops), so scripts can tell repair was refused.
TEST(cli_tool, repair_cli_refuses_active_secondary)
{
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--activate-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--repair"};
        EXPECT_EQ(1, main_impl(cout, cerr, args));
        EXPECT_NE(std::string::npos, cerr.str().find("active"));
    }
}

// End-to-end guard against the "wrong order" brick: running
// --activate-secondary on a still-buggy migrated pool must refuse (pointing at
// --repair) WITHOUT stamping the activate intent log, so the pool stays
// openable; --repair then fixes it and activation succeeds. Also covers the
// CLI --repair success path on an actually-broken pool.
TEST(cli_tool, activate_refuses_unrepaired_pool_then_repair_enables_activation)
{
    static constexpr off_t SECONDARY_CNV_CHUNK0_ID_OFFSET = 432 + 28;
    char temppath[] = "cli_tool_test_XXXXXX";
    make_temp_pool(temppath);
    auto const untempfile =
        monad::make_scope_exit([&]() noexcept { unlink(temppath); });
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
    }

    // Simulate the pre-fix migration artifact on the inactive secondary ring.
    {
        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        auto &cnv_chunk =
            pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::cnv, 0);
        auto const [write_fd, base_offset] = cnv_chunk.write_fd(0);
        auto const half_capacity = static_cast<off_t>(cnv_chunk.capacity() / 2);
        uint32_t const zero_id = 0;
        for (off_t copy_idx = 0; copy_idx < 2; copy_idx++) {
            ASSERT_EQ(
                4,
                ::pwrite(
                    write_fd,
                    &zero_id,
                    4,
                    off_t(base_offset) + copy_idx * half_capacity +
                        SECONDARY_CNV_CHUNK0_ID_OFFSET));
        }
        ASSERT_EQ(0, ::fsync(write_fd));
    }

    // 1. Activate refuses and points at --repair (no intent stamped).
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--activate-secondary"};
        EXPECT_EQ(1, main_impl(cout, cerr, args));
        EXPECT_NE(std::string::npos, cerr.str().find("--repair"));
    }
    // 2. Repair fixes the pool (CLI success path).
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--repair"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
        EXPECT_NE(
            std::string::npos, cout.str().find("Repaired secondary ring"));
    }
    // 3. Activation now succeeds — the refusal did not brick the pool.
    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--activate-secondary"};
        ASSERT_EQ(0, main_impl(cout, cerr, args)) << cerr.str();
        EXPECT_NE(std::string::npos, cout.str().find("Activated secondary"));
    }
    EXPECT_TRUE(read_secondary_active(temppath));
}

// Same shape as upgrade_migrates_monad007_pool, but the first cnv-chunk-0
// half is written as a partial pre-upgrade write: is_dirty=1 and a
// distinct history_length. The pre-migration heal must overwrite that
// half from the clean sibling before the migration loop runs, so the
// resulting MONAD008 pool reflects the clean half's history_length, not
// the corrupt one.
TEST(cli_tool, upgrade_heals_dirty_monad007_copy)
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

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--create"};
        ASSERT_EQ(0, main_impl(cout, cerr, args));
    }

    uint64_t const clean_history_length = 9999;
    uint64_t const corrupt_history_length = 0xDEADBEEFULL;

    {
        std::vector<std::filesystem::path> paths{temppath};
        MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags const flags;
        MONAD_ASYNC_NAMESPACE::storage_pool pool{
            std::span{paths},
            MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
            flags};
        uint32_t const chunk_count = static_cast<uint32_t>(
            pool.chunks(MONAD_ASYNC_NAMESPACE::storage_pool::seq));
        auto &cnv_chunk =
            pool.chunk(MONAD_ASYNC_NAMESPACE::storage_pool::cnv, 0);
        auto const [write_fd, base_offset] = cnv_chunk.write_fd(0);
        off_t const half_capacity = // NOLINT(misc-include-cleaner)
            static_cast<off_t>(cnv_chunk.capacity() / 2);

        auto const build_monad007_buf = [&](uint64_t const history_length,
                                            bool const dirty) {
            std::vector<uint8_t> buf(
                MONAD007_DB_METADATA_SIZE +
                    size_t(chunk_count) * sizeof(db_metadata::chunk_info_t),
                0);
            memcpy(
                buf.data(),
                db_metadata::PREVIOUS_MAGIC,
                db_metadata::MAGIC_STRING_LEN);
            // reserved_for_is_dirty_ occupies bits 56..63 of the 8-byte
            // bitfield word at offset 8 (i.e. byte 15), shared with the
            // MONAD008 layout.
            uint64_t bitfield = static_cast<uint64_t>(chunk_count) & 0xfffffULL;
            if (dirty) {
                bitfield |= uint64_t(1) << 56;
            }
            memcpy(buf.data() + 8, &bitfield, 8);
            uint32_t const high_bits_all_set = uint32_t(-1);
            uint32_t const cnv_len = 0;
            memcpy(buf.data() + 40, &high_bits_all_set, 4);
            memcpy(buf.data() + 44, &cnv_len, 4);
            memcpy(buf.data() + 524344, &history_length, 8);
            uint32_t const invalid = db_metadata::NULL_CHUNK;
            for (int i = 0; i < 6; i++) {
                memcpy(
                    buf.data() + MONAD007_LIST_TRIPLE_OFFSET + i * 4,
                    &invalid,
                    4);
            }
            return buf;
        };

        // Copy 0: dirty + corrupt history_length (simulates partial write).
        auto const dirty_buf =
            build_monad007_buf(corrupt_history_length, /*dirty=*/true);
        // Copy 1: clean + intended history_length.
        auto const clean_buf =
            build_monad007_buf(clean_history_length, /*dirty=*/false);

        ASSERT_EQ(
            ssize_t(dirty_buf.size()),
            ::pwrite( // NOLINT(misc-include-cleaner)
                write_fd,
                dirty_buf.data(),
                dirty_buf.size(),
                off_t(base_offset)));
        ASSERT_EQ(
            ssize_t(clean_buf.size()),
            ::pwrite( // NOLINT(misc-include-cleaner)
                write_fd,
                clean_buf.data(),
                clean_buf.size(),
                off_t(base_offset) + half_capacity));
        ASSERT_EQ(0, ::fsync(write_fd));
    }

    {
        std::stringstream cout;
        std::stringstream cerr;
        std::string_view args[] = {
            "monad-mpt", "--storage", temppath, "--upgrade"};
        int const retcode = main_impl(cout, cerr, args);
        ASSERT_EQ(0, retcode) << "stderr: " << cerr.str();
        EXPECT_NE(std::string::npos, cout.str().find("Success."));
    }

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
        // Without the heal, the migration loop would have set the dirty
        // bit during hold_dirty, performed an in-place migration on
        // corrupt bytes, then cleared the dirty bit on scope exit —
        // making the corrupt history_length indistinguishable from valid
        // data. The heal must overwrite the dirty copy with the clean
        // sibling before migration runs, so the survivor is the clean
        // value.
        EXPECT_EQ(m->history_length, clean_history_length);
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
