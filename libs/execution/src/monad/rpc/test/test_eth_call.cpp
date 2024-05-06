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
    static auto const headstate_file =
        test_resource::rpc_tests_dir / "headstate.json";

    void read_headstate(TrieDb &db)
    {
        StateDeltas state_deltas;
        Code code_deltas;
        std::ifstream ifile(headstate_file.c_str());
        auto const headstate_json = nlohmann::json::parse(ifile);
        for (auto const &[addr, acct] : headstate_json["accounts"].items()) {
            // address
            Address address{};
            auto const address_byte_string = evmc::from_hex(addr);
            MONAD_ASSERT(address_byte_string.has_value());
            std::copy_n(
                address_byte_string.value().begin(),
                address_byte_string.value().length(),
                address.bytes);

            // storage
            StorageDeltas storage_deltas;
            if (acct.contains("storage")) {
                for (auto const &[k, v] : acct.at("storage").items()) {
                    bytes32_t storage_key;
                    bytes32_t storage_value;
                    std::memcpy(
                        storage_key.bytes,
                        evmc::from_hex(k).value().data(),
                        32);

                    auto const storage_value_byte_string =
                        evmc::from_hex("0x" + v.get<std::string>()).value();
                    std::copy_n(
                        storage_value_byte_string.begin(),
                        storage_value_byte_string.length(),
                        storage_value.bytes);

                    storage_deltas.emplace(
                        storage_key, std::make_pair(NULL_HASH, storage_value));
                }
            }

            auto const balance =
                intx::from_string<uint256_t>(acct.at("balance"));
            auto const nonce = acct.at("nonce").get<uint64_t>();
            auto const code =
                acct.contains("code")
                    ? evmc::from_hex(acct.at("code").get<std::string>()).value()
                    : byte_string{};

            Account account{
                .balance = balance,
                .code_hash = code == byte_string{}
                                 ? NULL_HASH
                                 : std::bit_cast<bytes32_t>(ethash::keccak256(
                                       code.data(), code.size())),
                .nonce = nonce};

            state_deltas.emplace(
                address,
                StateDelta{
                    .account = {std::nullopt, account},
                    .storage = storage_deltas});
            if (code != byte_string{}) {
                code_deltas.emplace(
                    account.code_hash,
                    std::make_shared<CodeAnalysis>(analyze(code)));
            }
        }

        db.commit(state_deltas, code_deltas);
    }
};

TEST(Eth_Call, call_env)
{
    auto const *const name = tmpnam(nullptr);
    TrieDb db{mpt::OnDiskDbConfig{.dbname_paths{name}}};
    read_headstate(db);

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
    read_headstate(db);

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

    // test state override (code override)
    nlohmann::json override_json;
    override_json["0x000f3df6d732807ef1319fb7b8bb8522d0beac02"]["code"] =
        "0x366002146022577177726f6e672d63616c6c6461746173697a656000526012600efd"
        "5b60003560f01c61ff01146047576d77726f6e672d63616c6c64617461600052600e60"
        "12fd5b61ffee6000526002601ef3";

    Transaction const override_txn{
        .nonce = 0,
        .max_fee_per_gas = 0,
        .gas_limit = INT64_MAX,
        .value = 0,
        .to = 0x000f3df6d732807ef1319fb7b8bb8522d0beac02_address,
        .data = {0xff, 0x01}};

    auto const override_result = eth_call_helper(
        override_txn,
        header,
        0,
        0x0000000000000000000000000000000000000000_address,
        buffer,
        {name},
        override_json);

    EXPECT_FALSE(override_result.has_error());
    EXPECT_EQ(
        (byte_string_view{
            override_result.value().output_data,
            override_result.value().output_size}),
        (byte_string{0xff, 0xee}));

    std::filesystem::remove(name);
}

TEST(Eth_Call, empty_balance_transfer)
{
    static constexpr auto a =
        0x5353535353535353535353535353535353535353_address;
    static constexpr auto b =
        0xbebebebebebebebebebebebebebebebebebebebe_address;

    auto const *const name = tmpnam(nullptr);
    TrieDb db{mpt::OnDiskDbConfig{.dbname_paths{name}}};

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
        eth_call_helper(good_txn, header, 0, a, empty_buffer, {name});
    if (result.has_error()) {
        std::cout << result.assume_error().value() << std::endl;
    }
    MONAD_ASSERT(!result.has_error());

    EXPECT_EQ(result.value().status_code, EVMC_SUCCESS);

    // This txn would fail because of low gas_limit
    Transaction bad_txn{
        .nonce = 2,
        .max_fee_per_gas = 100,
        .gas_limit = 10'000,
        .value = 10'000,
        .to = std::make_optional(b),
        .type = TransactionType::legacy,
        .data = {}};

    auto const bad_result =
        eth_call_helper(bad_txn, header, 0, a, empty_buffer, {name});
    EXPECT_TRUE(bad_result.has_error());
}

TEST(Eth_Call, transfer_with_state_override)
{
    static constexpr auto a =
        0x5353535353535353535353535353535353535353_address;
    static constexpr auto b =
        0xbebebebebebebebebebebebebebebebebebebebe_address;

    auto const *const name = tmpnam(nullptr);
    TrieDb db{mpt::OnDiskDbConfig{.dbname_paths{name}}};

    Account acct_a{.balance = 100'000'000, .nonce = 1};
    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, acct_a}, .storage = {}}}},
        Code{});

    Transaction txn{
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
        eth_call_helper(txn, header, 0, a, empty_buffer, {name});
    if (result.has_error()) {
        std::cout << result.assume_error().value() << std::endl;
    }
    MONAD_ASSERT(!result.has_error());

    EXPECT_EQ(result.value().status_code, EVMC_SUCCESS);

    // Add state override, reduce A's balance so that call would fail
    nlohmann::json override_json;
    override_json["0x5353535353535353535353535353535353535353"]["balance"] =
        "1000";
    auto const bad_result =
        eth_call_helper(txn, header, 0, a, empty_buffer, {name}, override_json);
    EXPECT_TRUE(bad_result.has_error());
}
