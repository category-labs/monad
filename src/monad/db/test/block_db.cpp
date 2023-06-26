#include <monad/db/block_db.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

using namespace monad;
using namespace db;

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

TEST(BlockDb, should_be_in_cache)
{
    BlockDb db(test_resource::correct_block_data_dir);
    EXPECT_TRUE(db.should_be_in_cache(0));
    EXPECT_TRUE(db.should_be_in_cache(1));
}

// From etherscan.io
static constexpr auto zero_hash{
    0xd4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3_bytes32};
static constexpr auto one_hash{
    0x88e96d4537bea4d9c05d12549907b32561d3bf31f45aae734cdc119f13406cb6_bytes32};
static constexpr auto two_hash{
    0xb495a1d7e6663152ae92708da4843337b958146015a2802f4193a410044698c9_bytes32};
static constexpr auto fourteen_million_hash{
    0x9bff49171de27924fa958faf7b7ce605c1ff0fdee86f4c0c74239e6ae20d9446_bytes32};

TEST(BlockDb, get_hash_under_256)
{
    Block b{};
    BlockDb db(test_resource::correct_block_data_dir);
    auto res = db.get(0u, b);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);
    EXPECT_EQ(db.earliest_block_in_cache(), 0);

    auto const hash = db.get_block_hash(0u);
    EXPECT_EQ(hash, zero_hash);
}

TEST(BlockDb, get_hash_over_256)
{
    Block b{};
    BlockDb db(test_resource::correct_block_data_dir);
    auto res = db.get(14'000'000u, b);

    EXPECT_EQ(res, BlockDb::Status::SUCCESS);

    auto const hash = db.get_block_hash(14'000'000u);
    EXPECT_EQ(hash, fourteen_million_hash);
}

TEST(BlockDb, get_then_get_hash_previous_block)
{
    Block b{};
    BlockDb db(test_resource::correct_block_data_dir);

    auto res = db.get(2u, b);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);

    auto hash = db.get_block_hash(0u);
    EXPECT_EQ(hash, zero_hash);
    hash = db.get_block_hash(1u);
    EXPECT_EQ(hash, one_hash);
    hash = db.get_block_hash(2u);
    EXPECT_EQ(hash, two_hash);
}

static constexpr auto two_mil_0_hash{
    0xfa0e5ba976931459e7aff38ba3800dfb4e75ba52b185cd41973d013b62c30b90_bytes32};

TEST(BlockDb, get_then_get_then_get_hash_over_256)
{
    Block b{};
    BlockDb db(test_resource::correct_block_data_dir);

    auto res = db.get(2'730'002u, b);
    EXPECT_EQ(res, BlockDb::Status::SUCCESS);

    auto const hash1 = db.get_block_hash(2'730'000u);
    EXPECT_EQ(hash1, two_mil_0_hash);
    auto const hash2 = db.get_block_hash(2'729'745u);
    EXPECT_EQ(hash2, BlockDb::null);
}
