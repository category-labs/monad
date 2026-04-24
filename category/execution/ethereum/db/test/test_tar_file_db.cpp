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

#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/tar_file_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <charconv>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <map>
#include <string>
#include <system_error>
#include <unistd.h>
#include <vector>

using namespace monad;

namespace
{
    // Group the fixture files by their million-block bucket and invoke the
    // system `tar` to produce `<N>M.tar` files in `out_dir`. Returns the list
    // of block numbers that were tar'd, so tests can exercise them.
    std::vector<uint64_t>
    build_tar_fixture(std::filesystem::path const &out_dir)
    {
        std::filesystem::create_directories(out_dir);

        std::map<uint64_t, std::vector<std::string>> by_bucket;
        std::vector<uint64_t> all_blocks;
        for (auto const &entry : std::filesystem::directory_iterator{
                 test_resource::correct_block_data_dir}) {
            if (!entry.is_regular_file()) {
                continue;
            }
            auto const name = entry.path().filename().string();
            uint64_t num = 0;
            auto const res = std::from_chars(
                name.data(), name.data() + name.size(), num);
            if (res.ec != std::errc{} ||
                res.ptr != name.data() + name.size()) {
                continue;
            }
            by_bucket[num / 1'000'000].push_back(name);
            all_blocks.push_back(num);
        }

        for (auto const &[bucket, names] : by_bucket) {
            auto const tar_path =
                out_dir / (std::to_string(bucket) + "M.tar");
            std::string cmd = "tar cf '" + tar_path.string() + "' -C '" +
                              test_resource::correct_block_data_dir.string() +
                              "'";
            for (auto const &n : names) {
                cmd += " '" + n + "'";
            }
            [[maybe_unused]] auto const rc = std::system(cmd.c_str());
            EXPECT_EQ(rc, 0) << "tar failed for bucket " << bucket;
        }

        return all_blocks;
    }

    class TarFileDbTest : public ::testing::Test
    {
    protected:
        std::filesystem::path tmp_dir_;

        void SetUp() override
        {
            tmp_dir_ = std::filesystem::temp_directory_path() /
                       ("monad_tar_fixture_" +
                        std::to_string(::getpid()) + "_" +
                        std::to_string(reinterpret_cast<uintptr_t>(this)));
            std::filesystem::remove_all(tmp_dir_);
        }

        void TearDown() override
        {
            std::error_code ec;
            std::filesystem::remove_all(tmp_dir_, ec);
        }
    };
}

TEST_F(TarFileDbTest, AutodetectRecognizesTarDirectory)
{
    build_tar_fixture(tmp_dir_);
    EXPECT_TRUE(TarFileDb::looks_like_tar_backed(tmp_dir_));
    EXPECT_FALSE(TarFileDb::looks_like_tar_backed(
        test_resource::correct_block_data_dir));
}

TEST_F(TarFileDbTest, AutodetectRecognizesSingleTarFile)
{
    auto const blocks = build_tar_fixture(tmp_dir_);
    ASSERT_FALSE(blocks.empty());
    // Find the first produced *.tar file
    std::filesystem::path first_tar;
    for (auto const &e :
         std::filesystem::directory_iterator{tmp_dir_}) {
        if (e.path().extension() == ".tar") {
            first_tar = e.path();
            break;
        }
    }
    ASSERT_FALSE(first_tar.empty());
    EXPECT_TRUE(TarFileDb::looks_like_tar_backed(first_tar));
}

TEST_F(TarFileDbTest, BlockDbAutoPicksTarAndReadsAllFixtureBlocks)
{
    auto const blocks = build_tar_fixture(tmp_dir_);
    BlockDb const block_db(tmp_dir_, BlockDbFormat::Auto);
    for (auto const num : blocks) {
        Block block;
        EXPECT_TRUE(block_db.get(num, block))
            << "could not read block " << num << " from tar-backed BlockDb";
    }
}

TEST_F(TarFileDbTest, ExplicitTarFormatAgainstTarDirectory)
{
    auto const blocks = build_tar_fixture(tmp_dir_);
    ASSERT_FALSE(blocks.empty());
    BlockDb const block_db(tmp_dir_, BlockDbFormat::Tar);
    Block block;
    EXPECT_TRUE(block_db.get(blocks.front(), block));
}

TEST_F(TarFileDbTest, ExplicitFilesFormatPreservesExistingBehavior)
{
    // Point the Files backend at the on-disk fixture directory (no tars
    // there) and confirm it still works.
    BlockDb const block_db(
        test_resource::correct_block_data_dir, BlockDbFormat::Files);
    Block block;
    EXPECT_TRUE(block_db.get(46'402u, block));
}

TEST_F(TarFileDbTest, ParityWithFileDbBackendForSelectedBlocks)
{
    build_tar_fixture(tmp_dir_);
    BlockDb const tar_db(tmp_dir_, BlockDbFormat::Tar);
    BlockDb const files_db(
        test_resource::correct_block_data_dir, BlockDbFormat::Files);

    for (auto const num : {46'402u,
                           2'730'000u,
                           2'730'001u,
                           2'730'002u,
                           2'730'009u,
                           2'397'315u,
                           14'000'000u}) {
        Block via_tar;
        Block via_files;
        ASSERT_TRUE(tar_db.get(num, via_tar)) << "tar miss at " << num;
        ASSERT_TRUE(files_db.get(num, via_files)) << "files miss at " << num;
        EXPECT_EQ(via_tar.header.number, via_files.header.number);
        EXPECT_EQ(via_tar.header.state_root, via_files.header.state_root);
        EXPECT_EQ(via_tar.header.parent_hash, via_files.header.parent_hash);
        EXPECT_EQ(via_tar.transactions.size(), via_files.transactions.size());
    }
}

TEST_F(TarFileDbTest, MissingBlockReturnsFalseNotCrash)
{
    build_tar_fixture(tmp_dir_);
    BlockDb const block_db(tmp_dir_, BlockDbFormat::Tar);
    Block block;
    // Block 999999 is not in any fixture bucket's tar.
    EXPECT_FALSE(block_db.get(999'999u, block));
}
