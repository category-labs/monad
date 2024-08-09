#include <monad/core/block.hpp>
#include <monad/db/block_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <csignal>
#include <cstdint>

using namespace monad;

TEST(BrotliBlockDb, ReadNonExistingBlock)
{
    Block block;
    BrotliBlockDb const block_db(test_resource::correct_block_data_dir);
    // NO_BLOCK_FOUND
    EXPECT_FALSE(block_db.get(3u, block));
}

TEST(BrotliBlockDb, ReadNonDecompressableBlock)
{
    Block block;
    BrotliBlockDb const block_db(test_resource::bad_decompress_block_data_dir);
    // DECOMPRESS_ERROR
    EXPECT_EXIT(
        block_db.get(46'402u, block), testing::KilledBySignal(SIGABRT), "");
}

TEST(BrotliBlockDb, ReadNonDecodeableBlock)
{
    Block block;
    BrotliBlockDb const block_db(test_resource::bad_decode_block_data_dir);
    // DECODE_ERROR
    EXPECT_EXIT(
        block_db.get(46'402u, block), testing::KilledBySignal(SIGABRT), "");
}

TEST(BrotliBlockDb, CompressDecompressBlock46402)
{
    uint64_t const block_number = 46'402;

    // Read
    Block block;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730000)
{
    uint64_t const block_number = 2'730'000;

    // Read
    Block block;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730001)
{
    uint64_t const block_number = 2'730'001;

    // Read
    Block block;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730002)
{
    uint64_t const block_number = 2'730'002;

    // Read
    Block block;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730009)
{
    uint64_t const block_number = 2'730'009;

    // Read
    Block block;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompress14000000)
{
    uint64_t const block_number = 14'000'000;

    // Read
    Block block;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block);
    Block self_decoded_block;
    EXPECT_TRUE(block_db_read.get(block_number, self_decoded_block));
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, DecompressBlock2397315)
{
    uint64_t const block_number = 2'397'315;
    Block block;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.get(block_number, block));
}
