#include <monad/core/block.hpp>
#include <monad/db/block_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <csignal>
#include <cstdint>

using namespace monad;

TEST(BrotliBlockDb, ReadNonExistingBlock)
{
    BrotliBlockDb const block_db(test_resource::correct_block_data_dir);
    // NO_BLOCK_FOUND
    EXPECT_FALSE(block_db.read_block(3u).has_value());
}

TEST(BrotliBlockDb, ReadNonDecompressableBlock)
{
    BrotliBlockDb const block_db(test_resource::bad_decompress_block_data_dir);
    // DECOMPRESS_ERROR
    EXPECT_EXIT(
        block_db.read_block(46'402u), testing::KilledBySignal(SIGABRT), "");
}

TEST(BrotliBlockDb, ReadNonDecodeableBlock)
{
    BrotliBlockDb const block_db(test_resource::bad_decode_block_data_dir);
    // DECODE_ERROR
    EXPECT_EXIT(
        block_db.read_block(46'402u), testing::KilledBySignal(SIGABRT), "");
}

TEST(BrotliBlockDb, CompressDecompressBlock46402)
{
    uint64_t const block_number = 46'402;

    // Read
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    auto const block = block_db_read.read_block(block_number);
    EXPECT_TRUE(block.has_value());

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block.value());
    auto const self_decoded_block = block_db_read.read_block(block_number);
    EXPECT_TRUE(self_decoded_block.has_value());
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730000)
{
    uint64_t const block_number = 2'730'000;

    // Read
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);

    auto const block = block_db_read.read_block(block_number);
    EXPECT_TRUE(block.has_value());

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block.value());
    auto const self_decoded_block = block_db_read.read_block(block_number);
    EXPECT_TRUE(self_decoded_block.has_value());
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730001)
{
    uint64_t const block_number = 2'730'001;

    // Read
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    auto const block = block_db_read.read_block(block_number);
    EXPECT_TRUE(block.has_value());

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block.value());
    auto const self_decoded_block = block_db_read.read_block(block_number);
    EXPECT_TRUE(self_decoded_block.has_value());
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730002)
{
    uint64_t const block_number = 2'730'002;

    // Read
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    auto const block = block_db_read.read_block(block_number);
    EXPECT_TRUE(block.has_value());

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block.value());
    auto const self_decoded_block = block_db_read.read_block(block_number);
    EXPECT_TRUE(self_decoded_block.has_value());
    EXPECT_EQ(block, self_decoded_block.value());

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompressBlock2730009)
{
    uint64_t const block_number = 2'730'009;

    // Read
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    auto const block = block_db_read.read_block(block_number);
    EXPECT_TRUE(block.has_value());

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block.value());
    auto const self_decoded_block = block_db_read.read_block(block_number);
    EXPECT_TRUE(self_decoded_block.has_value());
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, CompressDecompress14000000)
{
    uint64_t const block_number = 14'000'000;

    // Read
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    auto const block = block_db_read.read_block(block_number);
    EXPECT_TRUE(block.has_value());

    // Compress
    BrotliBlockDb const block_db(test_resource::self_compressed_block_data_dir);
    block_db.remove(block_number);
    block_db.upsert(block_number, block.value());
    auto const self_decoded_block = block_db_read.read_block(block_number);
    EXPECT_TRUE(self_decoded_block.has_value());
    EXPECT_EQ(block, self_decoded_block);

    // Cleanup
    EXPECT_TRUE(block_db.remove(block_number));
}

TEST(BrotliBlockDb, DecompressBlock2397315)
{
    uint64_t const block_number = 2'397'315;
    BrotliBlockDb const block_db_read(test_resource::correct_block_data_dir);
    EXPECT_TRUE(block_db_read.read_block(block_number).has_value());
}
