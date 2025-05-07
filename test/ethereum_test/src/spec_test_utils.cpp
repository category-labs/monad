#include <from_json.hpp>
#include <spec_test_utils.hpp>

#include <monad/contract/storage_variable.hpp>
#include <monad/contract/uint256.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

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
        auto const db_addr_key = fmt::format("{}", addr_bytes);
        auto const db_addr_key_hashed =
            fmt::format("{}", to_bytes(keccak256(addr_bytes.bytes)));

        ASSERT_TRUE(db.contains(db_addr_key_hashed)) << db_addr_key;
        auto const &db_account = db.at(db_addr_key_hashed);

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

void validate_staking_post_state(nlohmann::json const &json, State &state)
{
    struct Bytes48
    {
        byte_string_fixed<48> bytes;
    };

    StakingContract contract{state, STAKING_CONTRACT_ADDRESS};
    auto const expected_balance = intx::from_string<uint256_t>(json["balance"]);
    auto const actual_balance =
        intx::be::load<uint256_t>(state.get_balance(STAKING_CONTRACT_ADDRESS));
    EXPECT_EQ(expected_balance, actual_balance) << fmt::format(
        "expected {}, actual {}", expected_balance, actual_balance);

    // contract constants
    EXPECT_EQ(
        intx::from_string<uint256_t>(json["epoch"]),
        contract.vars.epoch.load_unchecked().native());
    EXPECT_EQ(
        intx::from_string<uint256_t>(json["last_validator_id"]),
        contract.vars.last_validator_id.load_unchecked().native());
    EXPECT_EQ(
        intx::from_string<uint256_t>(json["last_delegate_request_id"]),
        contract.vars.last_delegate_request_id.load_unchecked().native());
    EXPECT_EQ(
        intx::from_string<uint256_t>(json["last_undelegate_request_id"]),
        contract.vars.last_undelegate_request_id.load_unchecked().native());

    auto const &validator_set_json = json["validator_set"];
    ASSERT_EQ(validator_set_json.size(), contract.vars.validator_set.length());
    for (size_t i = 0; i < validator_set_json.size(); ++i) {
        EXPECT_EQ(
            intx::from_string<uint256_t>(validator_set_json[i]),
            contract.vars.validator_set.get(i).load().value().native());
    }

    for (auto const &[epoch_json, delegate_queue_json] :
         json["delegate_queue"].items()) {

        auto const epoch = intx::from_string<Uint256Native>(epoch_json).to_be();
        auto const delegate_queue = contract.vars.delegate_queue(epoch);
        ASSERT_EQ(delegate_queue_json.size(), delegate_queue.length());

        for (size_t i = 0; i < delegate_queue_json.size(); ++i) {
            auto const expected_id =
                intx::from_string<uint256_t>(delegate_queue_json[i]);
            auto const actual_id = delegate_queue.get(i).load().value();
            EXPECT_EQ(expected_id, actual_id.native());
        }
    }

    for (auto const &[delegate_id_str, delegate_request_json] :
         json["delegate_request"].items()) {
        auto const id =
            intx::from_string<Uint256Native>(delegate_id_str).to_be();
        auto const request = contract.vars.delegate_request(id).load();
        ASSERT_TRUE(request.has_value())
            << "delegate_request: mapping not found: " << delegate_id_str;

        auto const expected_validator_id = intx::from_string<uint256_t>(
            delegate_request_json["validator_id"].get<std::string>());
        auto const expected_delegator =
            evmc::from_hex<Address>(
                delegate_request_json["delegator"].get<std::string>())
                .value();
        auto const expected_amount = intx::from_string<uint256_t>(
            delegate_request_json["amount"].get<std::string>());
        EXPECT_EQ(expected_validator_id, request->validator_id.native());
        EXPECT_EQ(expected_delegator, request->delegator);
        EXPECT_EQ(expected_amount, request->amount.native());
    }

    for (auto const &[validator_id_str, validator_info_json] :
         json["validator_info"].items()) {
        auto const validator_id =
            intx::from_string<Uint256Native>(validator_id_str).to_be();
        auto const validator_info =
            contract.vars.validator_info(validator_id).load();
        ASSERT_TRUE(validator_info.has_value())
            << "validator_info: mapping not found: " << validator_id_str;

        auto const expected_auth_address =
            evmc::from_hex<Address>(
                validator_info_json["auth_address"].get<std::string>())
                .value();
        auto const expected_bls_pubkey =
            evmc::from_hex<Bytes48>(
                validator_info_json["bls_pubkey"].get<std::string>())
                .value();
        auto const expected_active_stake =
            intx::from_string<uint256_t>(validator_info_json["active_stake"]);
        auto const expected_active_shares =
            intx::from_string<uint256_t>(validator_info_json["active_shares"]);
        auto const expected_rewards =
            intx::from_string<uint256_t>(validator_info_json["rewards"]);

        EXPECT_EQ(expected_auth_address, validator_info->auth_address);
        EXPECT_EQ(expected_bls_pubkey.bytes, validator_info->bls_pubkey);
        EXPECT_EQ(expected_active_stake, validator_info->active_stake.native());
        EXPECT_EQ(
            expected_active_shares, validator_info->active_shares.native());
        EXPECT_EQ(expected_rewards, validator_info->rewards.native());
    }

    for (auto const &[preimage_json, validator_id_str] :
         json["validator_id"].items()) {
        auto const preimage = evmc::from_hex<Address>(preimage_json).value();
        auto const expected =
            intx::from_string<Uint256Native>(validator_id_str);
        auto const mapping = contract.vars.validator_id(preimage).load();
        ASSERT_TRUE(mapping.has_value())
            << "validator_id: mapping not found: " << preimage_json;
        auto const actual = mapping.value().native();
        EXPECT_EQ(expected, actual);
    }

    for (auto const &[preimage_json, validator_id_str] :
         json["validator_id_bls"].items()) {
        auto const preimage = evmc::from_hex<Bytes48>(preimage_json).value();
        auto const expected =
            intx::from_string<Uint256Native>(validator_id_str);
        auto const mapping =
            contract.vars.validator_id_bls(preimage.bytes).load();
        ASSERT_TRUE(mapping.has_value())
            << "validator_id_bls: mapping not found: " << preimage_json;
        auto const actual = mapping.value().native();
        EXPECT_EQ(expected, actual);
    }
}

MONAD_TEST_NAMESPACE_END
