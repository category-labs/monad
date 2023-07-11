#include <monad/core/block.hpp>

#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>

#include <monad/execution/ethereum/genesis.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <fstream>

using namespace monad;
using namespace monad::execution;
using namespace monad::execution::ethereum;

template <typename TDB>
struct GenesisStateTest : public testing::Test
{
};

template <typename TDB>
struct GenesisStateRootTest : public testing::Test
{
};

using NoTrieDBTypes = ::testing::Types<db::InMemoryDB, db::RocksDB>;
using TrieDBTypes = ::testing::Types<db::InMemoryTrieDB, db::RocksTrieDB>;

TYPED_TEST_SUITE(GenesisStateTest, NoTrieDBTypes);
TYPED_TEST_SUITE(GenesisStateRootTest, TrieDBTypes);

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
        block_header.mix_hash,
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

TYPED_TEST(GenesisStateTest, read_ethereum_mainnet_genesis_state)
{
    using namespace intx;

    auto const genesis_file_path =
        test_resource::ethereum_genesis_dir / "mainnet.json";
    TypeParam db;

    std::ifstream ifile(genesis_file_path.c_str());
    auto const genesis_json = nlohmann::json::parse(ifile);
    read_genesis_state(genesis_json, db);

    address_t a1 = 0x3282791d6fd713f1e94f4bfd565eaa78b3a0599d_address;
    Account acct1{.balance = 0x487A9A304539440000_u256, .nonce = 0u};

    address_t a2 = 0x08411652c871713609af0062a8a1281bf1bbcfd9_address;
    Account acct2{.balance = 0x4BE4E7267B6AE00000_u256, .nonce = 0u};

    EXPECT_TRUE(db.contains(a1));
    EXPECT_EQ(db.at(a1), acct1);

    EXPECT_TRUE(db.contains(a2));
    EXPECT_EQ(db.at(a2), acct2);
}

TYPED_TEST(GenesisStateRootTest, ethereum_mainnet_genesis_state_root)
{
    auto const genesis_file_path =
        test_resource::ethereum_genesis_dir / "mainnet.json";
    TypeParam db;

    auto const block_header = read_genesis(genesis_file_path, db);

    // https://etherscan.io/block/0
    auto expected_state_root{
        0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544_bytes32};
    EXPECT_EQ(block_header.state_root, expected_state_root);
}
