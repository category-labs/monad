#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/genesis.hpp>

#include <evmc/evmc.hpp>

#include <nlohmann/json_fwd.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <fstream>
#include <optional>

using namespace monad;

TEST(Genesis, read_ethereum_mainnet_genesis_header)
{
    auto const genesis_file_path =
        test_resource::ethereum_genesis_dir / "mainnet.json";

    std::ifstream ifile(genesis_file_path.c_str());
    auto const genesis_json = nlohmann::json::parse(ifile);
    auto const block_header = read_genesis_blockheader(genesis_json);

    EXPECT_EQ(block_header.difficulty, 17179869184);
    auto const extra_data = byte_string(
        {0x11, 0xbb, 0xe8, 0xdb, 0x4e, 0x34, 0x7b, 0x4e, 0x8c, 0x93, 0x7c,
         0x1c, 0x83, 0x70, 0xe4, 0xb5, 0xed, 0x33, 0xad, 0xb3, 0xdb, 0x69,
         0xcb, 0xdb, 0x7a, 0x38, 0xe1, 0xe5, 0x0b, 0x1b, 0x82, 0xfa});

    EXPECT_EQ(block_header.extra_data, extra_data);
    EXPECT_EQ(block_header.gas_limit, 5000);
    EXPECT_EQ(
        block_header.prev_randao,
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32);
    EXPECT_EQ(
        block_header.nonce,
        byte_string_fixed<8UL>(
            {0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x42}));
    EXPECT_EQ(
        block_header.parent_hash,
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32);
    EXPECT_EQ(block_header.timestamp, 0);
}

TEST(Genesis, ethereum_mainnet_genesis_state_root)
{
    auto const genesis_file_path =
        test_resource::ethereum_genesis_dir / "mainnet.json";
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};

    auto const block_header = read_genesis(genesis_file_path, tdb);

    // https://etherscan.io/block/0
    auto expected_state_root{
        0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544_bytes32};
    EXPECT_EQ(block_header.state_root, expected_state_root);
}
