#include <monad/db/block_db.hpp>

#include <gtest/gtest.h>

#include <filesystem>

using namespace monad;
using namespace db;

// DATA_DIR needs to be the full path (/space/ssd....)
std::filesystem::__cxx11::path get_dir_path(int error_type = 0)
{
    auto env_path = std::getenv("DATA_DIR");
    if (env_path) {
        return std::filesystem::__cxx11::path(env_path);
    }
    else {
        auto monad_path = std::filesystem::current_path()
                              .parent_path()
                              .parent_path()
                              .parent_path()
                              .parent_path()
                              .parent_path();

        auto dir_path =
            monad_path / "test" / "common" / "blocks" / "compressed_blocks";
        if (error_type == 1) {
            dir_path = dir_path.parent_path() / "bad_decompress_blocks";
        }
        else if (error_type == 2) {
            dir_path = dir_path.parent_path() / "bad_decode_blocks";
        }

        return dir_path;
    }
}

TEST(BlockDb, ReadNonExistingBlock)
{
    Block block{};
    BlockDb block_db(get_dir_path());
    auto const res = block_db.get(1u, block);
    EXPECT_EQ(res, BlockDb::Status::NO_BLOCK_FOUND);
}

TEST(BlockDb, ReadNonDecompressableBlock)
{
    Block block{};
    BlockDb block_db(get_dir_path(1));
    auto const res = block_db.get(46'402u, block);
    EXPECT_EQ(res, BlockDb::Status::DECOMPRESS_ERROR);
}

TEST(BlockDb, ReadNonDecodeableBlock)
{
    Block block{};
    BlockDb block_db(get_dir_path(2));
    auto const res = block_db.get(46'402u, block);
    EXPECT_EQ(res, BlockDb::Status::DECODE_ERROR);
}

TEST(BlockDb, ReadBlock46402)
{
    Block block{};
    BlockDb block_db(get_dir_path());
    auto const res = block_db.get(46'402u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730000)
{
    Block block{};
    BlockDb block_db(get_dir_path());
    auto res = block_db.get(2'730'000u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730001)
{
    Block block{};
    BlockDb block_db(get_dir_path());
    auto res = block_db.get(2'730'001u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730002)
{
    Block block{};
    BlockDb block_db(get_dir_path());
    auto res = block_db.get(2'730'002u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730009)
{
    Block block{};
    BlockDb block_db(get_dir_path());
    auto res = block_db.get(2'730'009u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock14000000)
{
    Block block{};
    BlockDb block_db(get_dir_path());
    auto res = block_db.get(14'000'000u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}
