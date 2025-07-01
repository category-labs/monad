#include <monad/core/block.hpp>
#include <monad/db/block_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <csignal>
#include <cstdint>

using namespace monad;

TEST(BlockDb, ReadNonExistingBlock)
{
    Block block;
    BlockDb const block_db(test_resource::correct_block_data_dir);
    // NO_BLOCK_FOUND
    EXPECT_FALSE(block_db.get(CHAIN_CONFIG_ETHEREUM_MAINNET, 3u, block));
}

TEST(BlockDb, ReadNonDecompressableBlock)
{
    Block block;
    BlockDb const block_db(test_resource::bad_decompress_block_data_dir);
    // DECOMPRESS_ERROR
    EXPECT_EXIT(
        block_db.get(CHAIN_CONFIG_ETHEREUM_MAINNET, 46'402u, block),
        testing::KilledBySignal(SIGABRT),
        "");
}

TEST(BlockDb, ReadNonDecodeableBlock)
{
    Block block;
    BlockDb const block_db(test_resource::bad_decode_block_data_dir);
    // DECODE_ERROR
    EXPECT_EXIT(
        block_db.get(CHAIN_CONFIG_ETHEREUM_MAINNET, 46'402u, block),
        testing::KilledBySignal(SIGABRT),
        "");
}

TEST(BlockDb, CompressDecompressBlock46402)
{
    uint64_t const block_number = 46'402;

    // Read
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(
        block_db_read.get(CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, block));

    // Compress
    BlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(
        CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BlockDb, CompressDecompressBlock2730000)
{
    uint64_t const block_number = 2'730'000;

    // Read
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(
        block_db_read.get(CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, block));

    // Compress
    BlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(
        CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BlockDb, CompressDecompressBlock2730001)
{
    uint64_t const block_number = 2'730'001;

    // Read
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(
        block_db_read.get(CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, block));

    // Compress
    BlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(
        CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BlockDb, CompressDecompressBlock2730002)
{
    uint64_t const block_number = 2'730'002;

    // Read
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(
        block_db_read.get(CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, block));

    // Compress
    BlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(
        CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BlockDb, CompressDecompressBlock2730009)
{
    uint64_t const block_number = 2'730'009;

    // Read
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(
        block_db_read.get(CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, block));

    // Compress
    BlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(
        CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BlockDb, CompressDecompress14000000)
{
    uint64_t const block_number = 14'000'000;

    // Read
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(
        block_db_read.get(CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, block));

    // Compress
    BlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(
        CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BlockDb, DecompressBlock2397315)
{
    uint64_t const block_number = 2'397'315;
    Block block;
    BlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(
        block_db_read.get(CHAIN_CONFIG_ETHEREUM_MAINNET, block_number, block));
}
