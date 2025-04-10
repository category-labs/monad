#include <from_json.hpp>
#include <spec_test_utils.hpp>

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <evmc/hex.hpp>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <gtest/gtest.h>

#include <cstdint>

MONAD_TEST_NAMESPACE_BEGIN

void load_genesis_json_into_db(
    evmc_revision const rev, nlohmann::json const &j_contents, db_t &tdb)
{
    auto const genesisJson = j_contents.at("genesisBlockHeader");
    auto header = read_genesis_blockheader(genesisJson);
    ASSERT_EQ(
        NULL_ROOT,
        evmc::from_hex<bytes32_t>(
            genesisJson.at("transactionsTrie").get<std::string>())
            .value());
    ASSERT_EQ(
        NULL_ROOT,
        evmc::from_hex<bytes32_t>(
            genesisJson.at("receiptTrie").get<std::string>())
            .value());
    ASSERT_EQ(
        NULL_LIST_HASH,
        evmc::from_hex<bytes32_t>(
            genesisJson.at("uncleHash").get<std::string>())
            .value());
    ASSERT_EQ(
        bytes32_t{},
        evmc::from_hex<bytes32_t>(
            genesisJson.at("parentHash").get<std::string>())
            .value());

    std::optional<std::vector<Withdrawal>> withdrawals;
    if (rev >= EVMC_SHANGHAI) {
        ASSERT_EQ(
            NULL_ROOT,
            evmc::from_hex<bytes32_t>(
                genesisJson.at("withdrawalsRoot").get<std::string>())
                .value());
        withdrawals.emplace(std::vector<Withdrawal>{});
    }

    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};
    load_state_from_json(j_contents.at("pre"), state);
    bs.merge(state);
    bs.commit(
        MonadConsensusBlockHeader::from_eth_header(header),
        {} /* receipts */,
        {} /* call frames */,
        {} /* senders */,
        {} /* transactions */,
        {} /* ommers */,
        withdrawals);
    tdb.finalize(0, 0);
    ASSERT_EQ(
        to_bytes(keccak256(rlp::encode_block_header(tdb.read_eth_header()))),
        evmc::from_hex<bytes32_t>(genesisJson.at("hash").get<std::string>())
            .value());
}

void load_state_from_json(nlohmann::json const &j, State &state)
{
    for (auto const &[j_addr, j_acc] : j.items()) {
        auto const account_address =
            evmc::from_hex<monad::Address>(j_addr).value();

        if (j_acc.contains("code") || j_acc.contains("storage")) {
            ASSERT_TRUE(j_acc.contains("code") && j_acc.contains("storage"));
            state.create_contract(account_address);
        }

        if (j_acc.contains("code")) {
            state.set_code(
                account_address, j_acc.at("code").get<monad::byte_string>());
        }

        state.add_to_balance(
            account_address, j_acc.at("balance").get<intx::uint256>());
        // we cannot use the nlohmann::json from_json<uint64_t> because
        // it does not use the strtoull implementation, whereas we need
        // it so we can turn a hex string into a uint64_t
        state.set_nonce(
            account_address, integer_from_json<uint64_t>(j_acc.at("nonce")));

        if (j_acc.contains("storage")) {
            ASSERT_TRUE(j_acc["storage"].is_object());
            for (auto const &[key, value] : j_acc["storage"].items()) {
                nlohmann::json const key_json = key;
                monad::bytes32_t const key_bytes32 =
                    key_json.get<monad::bytes32_t>();
                monad::bytes32_t const value_bytes32 = value;
                if (value_bytes32 == monad::bytes32_t{}) {
                    // skip setting starting storage to zero to avoid pointless
                    // deletion
                    continue;
                }
                EXPECT_EQ(
                    state.set_storage(
                        account_address, key_bytes32, value_bytes32),
                    EVMC_STORAGE_ADDED);
            }
        }
    }
}

void validate_post_state(nlohmann::json const &json, nlohmann::json const &db)
{
    EXPECT_EQ(db.size(), json.size());

    for (auto const &[addr, j_account] : json.items()) {
        nlohmann::json const addr_json = addr;
        auto const addr_bytes = addr_json.get<Address>();
        auto const hashed_account = to_bytes(keccak256(addr_bytes.bytes));
        auto const db_addr_key = fmt::format("{}", hashed_account);

        ASSERT_TRUE(db.contains(db_addr_key)) << db_addr_key;
        auto const &db_account = db.at(db_addr_key);

        auto const expected_balance =
            fmt::format("{}", j_account.at("balance").get<uint256_t>());
        auto const expected_nonce = fmt::format(
            "0x{:x}", integer_from_json<uint64_t>(j_account.at("nonce")));
        auto const code = j_account.contains("code")
                              ? j_account.at("code").get<monad::byte_string>()
                              : monad::byte_string{};
        auto const expected_code = fmt::format(
            "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""));

        EXPECT_EQ(db_account.at("balance").get<std::string>(), expected_balance)
            << db_addr_key;
        EXPECT_EQ(db_account.at("nonce").get<std::string>(), expected_nonce)
            << db_addr_key;
        EXPECT_EQ(db_account.at("code").get<std::string>(), expected_code)
            << db_addr_key;

        auto const &db_storage = db_account.at("storage");
        EXPECT_EQ(db_storage.size(), j_account.at("storage").size())
            << db_addr_key;
        for (auto const &[key, j_value] : j_account.at("storage").items()) {
            nlohmann::json const key_json = key;
            auto const key_bytes = key_json.get<bytes32_t>();
            auto const db_storage_key =
                fmt::format("{}", to_bytes(keccak256(key_bytes.bytes)));
            ASSERT_TRUE(db_storage.contains(db_storage_key)) << db_storage_key;
            auto const expected_value =
                fmt::format("{}", j_value.get<bytes32_t>());
            EXPECT_EQ(db_storage.at(db_storage_key).at("value"), expected_value)
                << db_storage_key;
        }
    }
}

MONAD_TEST_NAMESPACE_END
