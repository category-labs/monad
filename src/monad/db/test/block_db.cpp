#include <monad/db/block_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

using namespace monad;

TEST(BlockDb, ReadNonExistingBlock)
{
    Block block{};
    BlockDb block_db(test_resource::correct_block_data_dir);
    auto const res = block_db.get(3u, block);
    EXPECT_EQ(res, BlockDb::Status::NO_BLOCK_FOUND);
}

TEST(BlockDb, ReadNonDecompressableBlock)
{
    Block block{};
    BlockDb block_db(test_resource::bad_decompress_block_data_dir);
    auto const res = block_db.get(46'402u, block);
    EXPECT_EQ(res, BlockDb::Status::DECOMPRESS_ERROR);
}

TEST(BlockDb, ReadNonDecodeableBlock)
{
    Block block{};
    BlockDb block_db(test_resource::bad_decode_block_data_dir);
    auto const res = block_db.get(46'402u, block);
    EXPECT_EQ(res, BlockDb::Status::DECODE_ERROR);
}

TEST(BlockDb, ReadBlock46402)
{
    Block block{};
    BlockDb block_db(test_resource::correct_block_data_dir);
    auto const res = block_db.get(46'402u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730000)
{
    Block block{};
    BlockDb block_db(test_resource::correct_block_data_dir);
    auto res = block_db.get(2'730'000u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730001)
{
    Block block{};
    BlockDb block_db(test_resource::correct_block_data_dir);
    auto res = block_db.get(2'730'001u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730002)
{
    Block block{};
    BlockDb block_db(test_resource::correct_block_data_dir);
    auto res = block_db.get(2'730'002u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock2730009)
{
    Block block{};
    BlockDb block_db(test_resource::correct_block_data_dir);
    auto res = block_db.get(2'730'009u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}

TEST(BlockDb, ReadBlock14000000)
{
    Block block{};
    BlockDb block_db(test_resource::correct_block_data_dir);
    auto res = block_db.get(14'000'000u, block);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
}
