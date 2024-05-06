#include <monad/core/block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/mpt/db.hpp>
#include <monad/rpc/config.hpp>
#include <monad/rpc/eth_call.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <test_resource_data.h>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <nlohmann/json.hpp>

#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <memory>
#include <optional>
#include <sstream>
#include <string>

using namespace monad;
using namespace monad::rpc;

namespace
{
    static auto const chain_rlp = test_resource::rpc_tests_dir / "chain.rlp";
    static auto const genesis = test_resource::rpc_tests_dir / "genesis.json";
    static auto const headstate =
        test_resource::rpc_tests_dir / "headstate.json";
    std::filesystem::path const db_path1 = "test1.db";
    std::filesystem::path const db_path2 = "test2.db";

    constexpr auto a = 0x5353535353535353535353535353535353535353_address;
    constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;

    std::string global_value;
};

TEST(Eth_Call, call_env)
{
    auto const *const name = tmpnam(nullptr);
    TrieDb db{mpt::OnDiskDbConfig{.dbname_paths{name}}};
    StateDeltas state_deltas;
    Code code;
    code.emplace(
        0x8e0388ecf64cfa76b3a6af159f77451519a7f9bb862e4cce24175c791fdcb0df_bytes32,
        std::make_shared<CodeAnalysis>(analyze(
            evmc::from_hex(
                "0x60004381526020014681526020014181526020014881526020014"
                "481526020013281526020013481526020016000f3")
                .value())));
    state_deltas.emplace(
        0x9344b07175800259691961298ca11c824e65032d_address,
        StateDelta{
            .account = {
                std::nullopt,
                Account{
                    .code_hash =
                        0x8e0388ecf64cfa76b3a6af159f77451519a7f9bb862e4cce24175c791fdcb0df_bytes32,
                    .nonce = 1}}});
    db.commit(state_deltas, code);

    BlockState block_state{db};
    State state{block_state, Incarnation{0, 0}};
    BlockHashBuffer buffer{};
    Transaction const txn{
        .nonce = 0,
        .max_fee_per_gas = 0,
        .gas_limit = INT64_MAX,
        .value = 0,
        .to = 0x9344b07175800259691961298ca11c824e65032d_address,
        .data = {}};
    BlockHeader header{
        .number = 1,
        .gas_limit = 0,
        .beneficiary = 0x0102030405010203040501020304050102030405_address,
        .base_fee_per_gas = std::nullopt,
    };
    auto const result = eth_call_helper(
        txn,
        header,
        0,
        0x0000000000000000000000000000000000000000_address,
        buffer,
        {name});
    EXPECT_FALSE(result.has_error());
    EXPECT_EQ(
        (byte_string_view{
            result.value().output_data, result.value().output_size}),
        (
            byte_string{
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, // block number
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, // chain id
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04,
                0x05, 0x01, 0x02, 0x03, 0x04, 0x05, 0x01, 0x02,
                0x03, 0x04, 0x05, 0x01, 0x02, 0x03, 0x04, 0x05, // coinbase
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // base fee
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // difficulty
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // origin
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // value
            }));
    std::filesystem::remove(name);
}

TEST(Eth_Call, call_contract)
{
    auto const *const name = tmpnam(nullptr);
    TrieDb db{mpt::OnDiskDbConfig{.dbname_paths{name}}};
    StateDeltas state_deltas;
    Code code;
    code.emplace(
        0x975f732458c1f6c2dd22b866b031cc509c6d4f788b1f020e351c1cdba48dacca_bytes32,
        std::make_shared<CodeAnalysis>(analyze(
            evmc::from_hex(
                "0x366002146022577177726f6e672d63616c6c6461746173697a6560005260"
                "12600efd5b60003560f01c61ff01146047576d77726f6e672d63616c6c6461"
                "7461600052600e6012fd5b61ffee6000526002601ef3")
                .value())));
    state_deltas.emplace(
        0x17e7eedce4ac02ef114a7ed9fe6e2f33feba1667_address,
        StateDelta{
            .account = {
                std::nullopt,
                Account{
                    .code_hash =
                        0x975f732458c1f6c2dd22b866b031cc509c6d4f788b1f020e351c1cdba48dacca_bytes32,
                    .nonce = 1}}});
    db.commit(state_deltas, code);

    BlockState block_state{db};
    State state{block_state, Incarnation{0, 0}};
    BlockHashBuffer buffer{};
    Transaction const txn{
        .nonce = 0,
        .max_fee_per_gas = 0,
        .gas_limit = INT64_MAX,
        .value = 0,
        .to = 0x17e7eedce4ac02ef114a7ed9fe6e2f33feba1667_address,
        .data = {0xff, 0x01}};
    BlockHeader header{
        .number = 0,
        .gas_limit = 0,
        .base_fee_per_gas = std::nullopt,
    };
    auto const result = eth_call_helper(
        txn,
        header,
        0,
        0x0000000000000000000000000000000000000000_address,
        buffer,
        {name});
    EXPECT_FALSE(result.has_error());
    EXPECT_EQ(
        (byte_string_view{
            result.value().output_data, result.value().output_size}),
        (byte_string{0xff, 0xee}));
    std::filesystem::remove(name);
}

TEST(Eth_Call, empty_balance_transfer)
{
    auto const config = std::make_optional(mpt::OnDiskDbConfig{
        .append = false,
        .compaction = false,
        .rd_buffers = 8192,
        .wr_buffers = 32,
        .uring_entries = 128,
        .sq_thread_cpu = 2,
        .dbname_paths = {db_path2}});

    TrieDb db{config};
    Account acct_a{.balance = 100'000'000, .nonce = 1};

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, acct_a}, .storage = {}}}},
        Code{});

    Transaction good_txn{
        .nonce = 2,
        .max_fee_per_gas = 100,
        .gas_limit = 50'000,
        .value = 10'000,
        .to = std::make_optional(b),
        .type = TransactionType::legacy,
        .data = {}};

    BlockHashBuffer empty_buffer{};
    BlockHeader header{
        .number = 0, .gas_limit = 10'000'000, .base_fee_per_gas = 1};

    auto const result =
        eth_call_helper(good_txn, header, 0, a, empty_buffer, {db_path2});
    if (result.has_error()) {
        std::cout << result.assume_error().value() << std::endl;
    }
    MONAD_ASSERT(!result.has_error());

    EXPECT_EQ(result.value().status_code, EVMC_SUCCESS);

    Transaction bad_txn{
        .nonce = 2,
        .max_fee_per_gas = 100,
        .gas_limit = 10'000,
        .value = 10'000,
        .to = std::make_optional(b),
        .type = TransactionType::legacy,
        .data = {}};

    auto const bad_result =
        eth_call_helper(bad_txn, header, 0, a, empty_buffer, {db_path2});
    EXPECT_TRUE(bad_result.has_error());
}
