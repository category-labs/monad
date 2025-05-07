#include <monad/contract/uint256.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/blake3.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/staking/secp256k1.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/execution/staking_contract.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>
#include <test_resource_data.h>

#include <cstdint>
#include <memory>
#include <utility>

#include <blst.h>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <secp256k1.h>

using namespace monad;
using namespace monad::test;
using namespace intx::literals;

namespace
{

    std::unique_ptr<secp256k1_context, decltype(&secp256k1_context_destroy)>
        secp_context(
            secp256k1_context_create(
                SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY),
            secp256k1_context_destroy);

    std::pair<blst_p1, blst_scalar>
    gen_bls_keypair(bytes32_t secret = bytes32_t{0x1000})
    {
        blst_scalar secret_key;
        blst_p1 public_key;

        blst_keygen(&secret_key, secret.bytes, sizeof(secret));
        blst_sk_to_pk_in_g1(&public_key, &secret_key);
        return {public_key, secret_key};
    }

    std::pair<secp256k1_pubkey, bytes32_t>
    gen_secp_keypair(bytes32_t secret = bytes32_t{0x1000})
    {
        secp256k1_pubkey public_key;

        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_create(
                     secp_context.get(), &public_key, secret.bytes));

        return {public_key, secret};
    }

    byte_string_fixed<33> serialize_secp_pubkey(secp256k1_pubkey const &pubkey)
    {
        byte_string_fixed<33> secp_pubkey_serialized;
        size_t size = 33;
        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_serialize(
                     secp_context.get(),
                     secp_pubkey_serialized.data(),
                     &size,
                     &pubkey,
                     SECP256K1_EC_COMPRESSED));
        MONAD_ASSERT(size == 33);
        return secp_pubkey_serialized;
    }

    byte_string_fixed<64>
    sign_secp(byte_string_view const message, bytes32_t const &seckey)
    {
        secp256k1_ecdsa_signature sig;
        auto const digest = blake3(message);
        MONAD_ASSERT(
            1 == secp256k1_ecdsa_sign(
                     secp_context.get(),
                     &sig,
                     digest.bytes,
                     seckey.bytes,
                     secp256k1_nonce_function_default,
                     NULL));

        byte_string_fixed<64> serialized;
        MONAD_ASSERT(
            1 == secp256k1_ecdsa_signature_serialize_compact(
                     secp_context.get(), serialized.data(), &sig));
        return serialized;
    }

    byte_string_fixed<96>
    sign_bls(byte_string_view const message, blst_scalar const &seckey)
    {
        static constexpr char DST[] =
            "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
        blst_p2 hash;
        blst_hash_to_g2(
            &hash,
            message.data(),
            message.size(),
            reinterpret_cast<uint8_t const *>(DST),
            sizeof(DST) - 1,
            nullptr,
            0);
        blst_p2 sig;
        blst_sign_pk_in_g1(&sig, &hash, &seckey);

        byte_string_fixed<96> serialized;
        blst_p2_compress(serialized.data(), &sig);
        return serialized;
    }

    byte_string craft_add_validator_input(
        Address const &auth_address, uint256_t const &stake)
    {
        auto const [bls_pubkey, bls_seckey] = gen_bls_keypair();
        auto const [secp_pubkey, secp_seckey] = gen_secp_keypair();

        auto const secp_pubkey_serialized = serialize_secp_pubkey(secp_pubkey);
        auto const bls_pubkey_serialized = [&bls_pubkey] {
            byte_string_fixed<48> serialized;
            blst_p1_compress(serialized.data(), &bls_pubkey);
            return serialized;
        }();

        byte_string input;
        input += to_byte_string_view(secp_pubkey_serialized);
        input += to_byte_string_view(bls_pubkey_serialized);
        input += to_byte_string_view(auth_address.bytes);
        input += to_byte_string_view(intx::be::store<bytes32_t>(stake).bytes);

        // sign with both keys
        byte_string_view const message = input;
        auto const secp_sig_serialized = sign_secp(message, secp_seckey);
        auto const bls_sig_serialized = sign_bls(message, bls_seckey);

        input += to_byte_string_view(secp_sig_serialized);
        input += to_byte_string_view(bls_sig_serialized);

        return input;
    }

    byte_string craft_undelegate_input(
        Uint256BE const &validator_id, Uint256BE const &amount)
    {
        byte_string input;
        input += byte_string_view{
            reinterpret_cast<uint8_t const *>(&validator_id),
            sizeof(Uint256BE)};
        input += byte_string_view{
            reinterpret_cast<uint8_t const *>(&amount), sizeof(Uint256BE)};

        return input;
    }
}

struct Stake : public ::testing::Test
{
    OnDiskMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};

    void SetUp() override
    {
        commit_sequential(
            tdb,
            StateDeltas{
                {STAKING_CONTRACT_ADDRESS,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 0, .nonce = 1}}}}},
            Code{},
            BlockHeader{});
        state.touch(STAKING_CONTRACT_ADDRESS);
    }
};

TEST_F(Stake, add_validator_invalid_input_size)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(uint256_t{1e18});

    byte_string_view too_short{};
    auto res = contract.precompile_add_validator(too_short, sender, value);
    EXPECT_EQ(res.status, StakingContract::INVALID_INPUT);

    byte_string too_long(2000, 0xa);
    res = contract.precompile_add_validator(too_short, sender, value);
    EXPECT_EQ(res.status, StakingContract::INVALID_INPUT);
}

TEST_F(Stake, add_validator_bad_signature)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(uint256_t{1e18});
    auto const input =
        craft_add_validator_input(0xababab_address, uint256_t{1e18});
    auto const message = input.substr(0, 133);

    auto const good_secp_keys = gen_secp_keypair();
    auto const bad_secp_keys = gen_secp_keypair(bytes32_t{0x2000});
    auto const good_bls_keys = gen_bls_keypair();
    auto const bad_bls_keys = gen_bls_keypair(bytes32_t{0x2000});

    // bad secp signature
    {
        byte_string input;
        input += message;
        input += to_byte_string_view(sign_secp(message, bad_secp_keys.second));
        input += to_byte_string_view(sign_bls(message, good_bls_keys.second));
        auto res = contract.precompile_add_validator(input, sender, value);
        EXPECT_EQ(
            res.status, StakingContract::SECP_SIGNATURE_VERIFICATION_FAILED);
    }

    // bad bls signature
    {
        byte_string input;
        input += message;
        input += to_byte_string_view(sign_secp(message, good_secp_keys.second));
        input += to_byte_string_view(sign_bls(message, bad_bls_keys.second));
        auto res = contract.precompile_add_validator(input, sender, value);
        EXPECT_EQ(
            res.status, StakingContract::BLS_SIGNATURE_VERIFICATION_FAILED);
    }
}

TEST_F(Stake, add_validator_msg_value_not_signed)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(uint256_t{1e18});
    auto const input =
        craft_add_validator_input(0xababab_address, uint256_t{2e18});
    auto const res = contract.precompile_add_validator(input, sender, value);
    EXPECT_EQ(res.status, StakingContract::INVALID_INPUT);
}

TEST_F(Stake, add_validator_already_exists)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(MIN_STAKE_AMOUNT);
    auto const input =
        craft_add_validator_input(0xababab_address, MIN_STAKE_AMOUNT);
    EXPECT_EQ(
        contract.precompile_add_validator(input, sender, value).status,
        StakingContract::SUCCESS);
    EXPECT_EQ(
        contract.precompile_add_validator(input, sender, value).status,
        StakingContract::VALIDATOR_EXISTS);
}

TEST_F(Stake, add_validator_minimum_stake_not_met)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(uint256_t{1});
    auto const input =
        craft_add_validator_input(0xababab_address, uint256_t{1});
    auto const res = contract.precompile_add_validator(input, sender, value);
    EXPECT_EQ(res.status, StakingContract::MINIMUM_STAKE_NOT_MET);
}

TEST_F(Stake, add_validator_then_remove)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const stake = 50000000000000000000_u256;
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(stake);
    auto const input = craft_add_validator_input(0xababab_address, stake);
    EXPECT_EQ(
        contract.precompile_add_validator(input, sender, value).status,
        StakingContract::SUCCESS);
    auto const validator_id = contract.vars.last_validator_id.load();
    ASSERT_TRUE(validator_id.has_value());
    EXPECT_EQ(validator_id.value(), Uint256Native{1}.to_be());

    auto const bls_keys = gen_bls_keypair();
    byte_string_fixed<48> bls_serialized;
    blst_p1_compress(bls_serialized.data(), &bls_keys.first);

    auto validator_info =
        contract.vars.validator_info(validator_id.value()).load();
    ASSERT_TRUE(validator_info.has_value());
    EXPECT_EQ(validator_info->auth_address, 0xababab_address);
    EXPECT_EQ(validator_info->bls_pubkey, bls_serialized);
    EXPECT_EQ(validator_info->active_stake, Uint256BE{});
    EXPECT_EQ(validator_info->active_shares, Uint256BE{});
    EXPECT_EQ(validator_info->rewards, Uint256BE{});

    ASSERT_FALSE(contract.vars.epoch.load().has_value()); // epoch 0
    auto const delegate_queue =
        contract.vars.delegate_queue(Uint256Native{1}.to_be());
    auto const undelegate_queue =
        contract.vars.undelegate_queue(Uint256Native{1}.to_be());
    EXPECT_EQ(delegate_queue.length(), 1);
    EXPECT_EQ(undelegate_queue.length(), 0);

    auto const delegate_request_id = delegate_queue.get(0).load();
    ASSERT_TRUE(delegate_request_id.has_value());
    EXPECT_EQ(delegate_request_id.value(), Uint256Native{1}.to_be());

    auto const delegate_request =
        contract.vars.delegate_request(delegate_request_id.value()).load();
    ASSERT_TRUE(delegate_request.has_value());
    EXPECT_EQ(delegate_request->validator_id, validator_id.value());
    EXPECT_EQ(delegate_request->delegator, 0xababab_address);
    EXPECT_EQ(delegate_request->amount, Uint256Native{stake}.to_be());

    contract.vars.epoch.store(Uint256Native{1}.to_be());
    ASSERT_FALSE(contract.syscall_on_epoch_change().has_error());
    EXPECT_EQ(delegate_queue.length(), 0);

    validator_info = contract.vars.validator_info(validator_id.value()).load();
    ASSERT_TRUE(validator_info.has_value());
    EXPECT_EQ(validator_info->auth_address, 0xababab_address);
    EXPECT_EQ(validator_info->bls_pubkey, bls_serialized);
    EXPECT_EQ(validator_info->active_stake, Uint256Native{stake}.to_be());
    EXPECT_EQ(validator_info->active_shares, Uint256Native{stake}.to_be());
    EXPECT_EQ(validator_info->rewards, Uint256BE{});

    byte_string undelegate_payload = craft_undelegate_input(
        validator_id.value(), Uint256Native{stake}.to_be());
    EXPECT_EQ(
        contract
            .precompile_undelegate(
                undelegate_payload, 0xababab_address, evmc_uint256be{})
            .status,
        StakingContract::SUCCESS);

    auto const delegate_queue2 =
        contract.vars.delegate_queue(Uint256Native{2}.to_be());
    auto const undelegate_queue2 =
        contract.vars.undelegate_queue(Uint256Native{2}.to_be());
    EXPECT_EQ(delegate_queue2.length(), 0);
    EXPECT_EQ(undelegate_queue2.length(), 1);
    EXPECT_EQ(contract.vars.validator_set.length(), 1);

    // delete validator
    auto const undelegate_request_id = undelegate_queue2.get(0).load();
    ASSERT_TRUE(undelegate_request_id.has_value());
    EXPECT_EQ(undelegate_request_id.value(), Uint256Native{1}.to_be());
    auto const undelegate_request =
        contract.vars.undelegate_request(undelegate_request_id.value()).load();
    ASSERT_TRUE(undelegate_request.has_value());
    EXPECT_EQ(undelegate_request->validator_id, validator_id.value());
    EXPECT_EQ(undelegate_request->delegator, 0xababab_address);
    EXPECT_EQ(undelegate_request->shares, Uint256Native{stake}.to_be());

    contract.vars.epoch.store(Uint256Native{2}.to_be());
    ASSERT_FALSE(contract.syscall_on_epoch_change().has_error());
    contract.vars.epoch.store(Uint256Native{3}.to_be());
    ASSERT_FALSE(contract.syscall_on_epoch_change().has_error());
    EXPECT_EQ(delegate_queue.length(), 0);
    EXPECT_EQ(contract.vars.validator_set.length(), 0);
}

TEST_F(Stake, reward_unknown_validator)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const val_address = Address{0xabcdef};
    auto const res = contract.syscall_reward_validator(val_address);
    ASSERT_TRUE(res.has_error());
    EXPECT_EQ(res.assume_error(), StakingSyscallError::BlockAuthorNotInSet);
}

TEST_F(Stake, reward_success)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(MIN_STAKE_AMOUNT);
    auto const input =
        craft_add_validator_input(0xababab_address, MIN_STAKE_AMOUNT);
    auto const res = contract.precompile_add_validator(input, sender, value);
    EXPECT_EQ(res.status, StakingContract::SUCCESS);
    EXPECT_TRUE(contract.vars.last_validator_id.load().has_value());
    EXPECT_EQ(
        contract.vars.last_validator_id.load().value(),
        Uint256Native{1}.to_be());
    auto const valinfo_storage = contract.vars.validator_info(
        contract.vars.last_validator_id.load().value());
    EXPECT_TRUE(valinfo_storage.load().has_value());

    EXPECT_FALSE(contract.vars.epoch.load().has_value());
    contract.vars.epoch.store(Uint256Native{1}.to_be());
    ASSERT_FALSE(contract.syscall_on_epoch_change().has_error());
    EXPECT_EQ(
        valinfo_storage.load()->active_stake,
        Uint256Native{MIN_STAKE_AMOUNT}.to_be());
    EXPECT_EQ(
        valinfo_storage.load()->active_shares,
        Uint256Native{MIN_STAKE_AMOUNT}.to_be());

    auto const secpkeys = gen_secp_keypair();
    byte_string_fixed<65> serialized;
    size_t uncompressed_pubkey_size = 65;
    secp256k1_ec_pubkey_serialize(
        secp_context.get(),
        serialized.data(),
        &uncompressed_pubkey_size,
        &secpkeys.first,
        SECP256K1_EC_UNCOMPRESSED);
    ASSERT_EQ(uncompressed_pubkey_size, 65);
    auto const val_address = address_from_secpkey(serialized);
    ASSERT_FALSE(contract.syscall_reward_validator(val_address).has_error());
    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(STAKING_CONTRACT_ADDRESS)),
        BASE_STAKING_REWARD);

    contract.vars.epoch.store(Uint256Native{2}.to_be());
    ASSERT_FALSE(contract.syscall_on_epoch_change().has_error());
    EXPECT_EQ(
        valinfo_storage.load()->active_stake,
        Uint256Native{MIN_STAKE_AMOUNT + BASE_STAKING_REWARD}.to_be());
    EXPECT_EQ(
        valinfo_storage.load()->active_shares,
        Uint256Native{MIN_STAKE_AMOUNT}
            .to_be()); // active shares shouldn't change
}

TEST_F(Stake, invoke_fallback)
{
    StakingContract contract(state, STAKING_CONTRACT_ADDRESS);
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(MIN_STAKE_AMOUNT);

    byte_string_fixed<8> const signature_bytes = {0xff, 0xff, 0xff, 0xff};
    auto signature = to_byte_string_view(signature_bytes);
    auto const [func, cost] = contract.precompile_dispatch(signature);
    EXPECT_EQ(cost, 0);

    auto const res = (contract.*func)(byte_string_view{}, sender, value);
    EXPECT_EQ(res.status, StakingContract::METHOD_NOT_SUPPORTED);
}
