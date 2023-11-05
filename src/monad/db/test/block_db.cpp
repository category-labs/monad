#include <monad/core/block.hpp>
#include <monad/db/block_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <csignal>

using namespace monad;

TEST(BlockDb, ReadNonExistingBlock)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(3u, block);
    EXPECT_FALSE(res); // NO_BLOCK_FOUND
}

TEST(BlockDb, ReadNonDecompressableBlock)
{
    Block block{};
    BlockDb const block_db(test_resource::bad_decompress_block_data_dir);
    // DECOMPRESS_ERROR
    EXPECT_EXIT(
        block_db.get(46'402u, block), testing::KilledBySignal(SIGABRT), "");
}

TEST(BlockDb, ReadNonDecodeableBlock)
{
    Block block{};
    BlockDb const block_db(test_resource::bad_decode_block_data_dir);
    // DECODE_ERROR
    EXPECT_EXIT(
        block_db.get(46'402u, block), testing::KilledBySignal(SIGABRT), "");
}

TEST(BlockDb, ReadBlock46402)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(46'402u, block);
    EXPECT_TRUE(res);
}

TEST(BlockDb, ReadBlock2730000)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(2'730'000u, block);
    EXPECT_TRUE(res);
}

TEST(BlockDb, ReadBlock2730001)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(2'730'001u, block);
    EXPECT_TRUE(res);
}

TEST(BlockDb, ReadBlock2730002)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(2'730'002u, block);
    EXPECT_TRUE(res);
}

TEST(BlockDb, ReadBlock2730009)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(2'730'009u, block);
    EXPECT_TRUE(res);
}

TEST(BlockDb, ReadBlock14000000)
{
    Block block{};
    BlockDb const block_db(test_resource::correct_block_data_dir);
    bool const res = block_db.get(14'000'000u, block);
    EXPECT_TRUE(res);
}
