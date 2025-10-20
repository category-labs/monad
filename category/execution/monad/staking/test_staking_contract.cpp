// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_decode_error.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/int_fmt.hpp> // NOLINT
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/bls.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/secp256k1.hpp>
#include <category/execution/monad/staking/util/staking_error.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <test_resource_data.h>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <cstdint>
#include <memory>
#include <ranges>
#include <utility>
#include <vector>

#include <blst.h>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <secp256k1.h>

using namespace monad;
using namespace monad::staking;
using namespace monad::test;

namespace
{

    constexpr uint256_t REWARD{1 * MON};

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

    byte_string_fixed<65>
    serialize_secp_pubkey_uncompressed(secp256k1_pubkey const &pubkey)
    {
        byte_string_fixed<65> secp_pubkey_serialized;
        size_t size = 65;
        MONAD_ASSERT(
            1 == secp256k1_ec_pubkey_serialize(
                     secp_context.get(),
                     secp_pubkey_serialized.data(),
                     &size,
                     &pubkey,
                     SECP256K1_EC_UNCOMPRESSED));
        MONAD_ASSERT(size == 65);
        return secp_pubkey_serialized;
    }

    std::tuple<byte_string, byte_string, byte_string, Address>
    craft_add_validator_input_raw(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0, bytes32_t secret = bytes32_t{0x1000})
    {
        auto const [bls_pubkey, bls_seckey] = gen_bls_keypair(secret);
        auto const [secp_pubkey, secp_seckey] = gen_secp_keypair(secret);

        auto const secp_pubkey_serialized = serialize_secp_pubkey(secp_pubkey);
        auto const bls_pubkey_serialized = [&bls_pubkey] {
            byte_string_fixed<48> serialized;
            blst_p1_compress(serialized.data(), &bls_pubkey);
            return serialized;
        }();

        auto const sign_address = address_from_secpkey(
            serialize_secp_pubkey_uncompressed(secp_pubkey));

        byte_string message;
        message += to_byte_string_view(secp_pubkey_serialized);
        message += to_byte_string_view(bls_pubkey_serialized);
        message += to_byte_string_view(auth_address.bytes);
        message += to_byte_string_view(intx::be::store<bytes32_t>(stake).bytes);
        message += to_byte_string_view(u256_be{commission}.bytes);

        // sign with both keys
        byte_string const secp_sig{
            to_byte_string_view(sign_secp(message, secp_seckey))};
        byte_string const bls_sig{
            to_byte_string_view(sign_bls(message, bls_seckey))};

        return {message, secp_sig, bls_sig, sign_address};
    }

    std::pair<byte_string, Address> craft_add_validator_input(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0, bytes32_t secret = bytes32_t{0x1000})
    {
        auto const [message, secp_sig, bls_sig, sign_address] =
            craft_add_validator_input_raw(
                auth_address, stake, commission, secret);
        AbiEncoder encoder;
        encoder.add_bytes(message);
        encoder.add_bytes(secp_sig);
        encoder.add_bytes(bls_sig);
        return {encoder.encode_final(), sign_address};
    }

    byte_string craft_undelegate_input(
        u64_be const val_id, uint256_t const &amount, u8_be const withdrawal_id)
    {
        AbiEncoder encoder;
        encoder.add_uint(val_id);
        encoder.add_uint<u256_be>(amount);
        encoder.add_uint(withdrawal_id);
        return encoder.encode_final();
    }

    byte_string
    craft_withdraw_input(u64_be const val_id, u8_be const withdrawal_id)
    {
        AbiEncoder encoder;
        encoder.add_uint(val_id);
        encoder.add_uint(withdrawal_id);
        return encoder.encode_final();
    }

    byte_string craft_change_commission_input(
        u64_be const val_id, uint256_t const &commission)
    {
        AbiEncoder encoder;
        encoder.add_uint(val_id);
        encoder.add_uint<u256_be>(commission);
        return encoder.encode_final();
    }
}

struct Stake : public ::testing::Test
{
    OnDiskMachine machine;
    vm::VM vm;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};
    NoopCallTracer call_tracer{};
    StakingContract<MonadTraits<MONAD_FOUR>> contract{state, call_tracer};

    void SetUp() override
    {
        commit_sequential(
            tdb,
            StateDeltas{
                {STAKING_CA,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 0, .nonce = 1}}}}},
            Code{},
            BlockHeader{});
        state.add_to_balance(STAKING_CA, 0); // create account like a txn would
        u64_be start_epoch{1};
        contract.vars.epoch.store(start_epoch);
    }

    void post_call(bool err)
    {
        if (!err) {
            state.pop_accept();
        }
        else {
            state.pop_reject();
        }
    }

    void inc_epoch()
    {
        uint64_t const next_epoch = contract.vars.epoch.load().native() + 1;
        (void)syscall_on_epoch_change(next_epoch);
    }

    void skip_to_next_epoch()
    {
        (void)syscall_snapshot();
        (void)inc_epoch();
    }

    void pull_delegator_up_to_date(u64_be const val_id, Address const &address)
    {
        AbiEncoder encoder;
        encoder.add_uint(val_id);
        encoder.add_address(address);
        (void)contract.precompile_get_delegator(
            encoder.encode_final(), address, {});
    }

    struct ValResult
    {
        u64_be id;
        Address sign_address;
    };

    void check_delegator_c_state(
        ValResult const &val, Address const &delegator,
        uint256_t expected_stake, uint256_t expected_rewards)
    {
        auto del = contract.vars.delegator(val.id, delegator);
        pull_delegator_up_to_date(val.id, delegator);

        EXPECT_EQ(del.stake().load().native(), expected_stake);
        EXPECT_EQ(del.rewards().load().native(), expected_rewards);
    }

    void check_delegator_zero(u64_be const val_id, Address const &delegator)
    {
        auto del = contract.vars.delegator(val_id, delegator);
        pull_delegator_up_to_date(val_id, delegator);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.accumulated_reward_per_token().load().native(), 0);
        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch(), 0);
        EXPECT_EQ(del.get_next_delta_epoch(), 0);
    }

    Result<void> syscall_snapshot()
    {
        state.push();
        auto res = contract.syscall_snapshot({}, 0);
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<void> syscall_on_epoch_change(uint64_t const epoch)
    {
        auto const input = abi_encode_uint<u64_be>(epoch);
        state.push();
        auto res = contract.syscall_on_epoch_change(input, 0);
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<void>
    syscall_reward(Address const &address, uint256_t const &raw_reward = REWARD)
    {
        auto const input = abi_encode_address(address);
        state.push();
        auto res = contract.syscall_reward(input, raw_reward);
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<ValResult> add_validator(
        Address const &auth_address, uint256_t const &stake,
        uint256_t const &commission = 0,
        bytes32_t const &secret = bytes32_t{0x1000})
    {
        auto const [input, sign_address] =
            craft_add_validator_input(auth_address, stake, commission, secret);
        auto const msg_value = intx::be::store<evmc_uint256be>(stake);
        state.push();
        auto res =
            contract.precompile_add_validator(input, auth_address, msg_value);
        post_call(res.has_error());
        BOOST_OUTCOME_TRY(auto const id_output, std::move(res));
        u64_be val_id = 0;
        state.add_to_balance(STAKING_CA, stake);
        std::memcpy(val_id.bytes, id_output.data() + 24, 8);
        return ValResult{.id = val_id, .sign_address = sign_address};
    }

    Result<void> delegate(
        u64_be const val_id, Address const &del_address, uint256_t const &stake)
    {
        auto const input = abi_encode_uint<u64_be>(val_id);
        auto const msg_value = intx::be::store<evmc_uint256be>(stake);
        state.push();
        auto res = contract.precompile_delegate(input, del_address, msg_value);
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        state.add_to_balance(STAKING_CA, stake);
        return outcome::success();
    }

    Result<void> undelegate(
        u64_be const val_id, Address const &address, u8_be const withdrawal_id,
        uint256_t const &amount)
    {
        auto const input =
            craft_undelegate_input(val_id, amount, withdrawal_id);
        state.push();
        auto res = contract.precompile_undelegate(input, address, {});
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<void> withdraw(
        u64_be const val_id, Address const &address, u8_be const withdrawal_id)
    {
        auto const input = craft_withdraw_input(val_id, withdrawal_id);
        state.push();
        auto res = contract.precompile_withdraw(input, address, {});
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<void> compound(u64_be const val_id, Address const &address)
    {
        auto const input = abi_encode_uint<u64_be>(val_id);
        state.push();
        auto res = contract.precompile_compound(input, address, {});
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<void> claim_rewards(u64_be const val_id, Address const &address)
    {
        auto const input = abi_encode_uint<u64_be>(val_id);
        state.push();
        auto res = contract.precompile_claim_rewards(input, address, {});
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<void> change_commission(
        u64_be const val_id, Address const &sender, uint256_t const &commission)
    {
        auto const input = craft_change_commission_input(val_id, commission);
        state.push();
        auto res = contract.precompile_change_commission(input, sender, {});
        post_call(res.has_error());
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<void> external_reward(
        u64_be const val_id, Address const &sender, uint256_t const &reward)
    {
        auto const input = abi_encode_uint<u64_be>(val_id);
        auto const msg_value = intx::be::store<evmc_uint256be>(reward);
        state.push();
        auto res =
            contract.precompile_external_reward(input, sender, msg_value);
        post_call(res.has_error());
        state.add_to_balance(STAKING_CA, reward);
        BOOST_OUTCOME_TRYV(std::move(res));
        return outcome::success();
    }

    Result<byte_string> get_valset(uint32_t const start_index)
    {
        return contract.precompile_get_consensus_valset(
            abi_encode_uint<u32_be>(start_index), {}, {});
    }

    uint256_t get_balance(Address const &account)
    {
        return intx::be::load<uint256_t>(state.get_balance(account));
    }
};

TEST_F(Stake, invoke_fallback)
{
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);

    byte_string_fixed<8> const signature_bytes = {0xff, 0xff, 0xff, 0xff};
    auto signature = to_byte_string_view(signature_bytes);
    auto const [func, cost] = contract.precompile_dispatch(signature);
    EXPECT_EQ(cost, 40000);

    auto const res = (contract.*func)(byte_string_view{}, sender, value);
    EXPECT_EQ(res.assume_error(), StakingError::MethodNotSupported);
}

// Check that accumulator is monotonically increasing - Done
// Check that accumulator is updating principle + reward amount correctly
TEST_F(Stake, accumulator_is_monotonic_again)
{
    // Add validator
    auto const val = add_validator(0xdeadbeef_address, ACTIVE_VALIDATOR_STAKE);
    EXPECT_FALSE(val.has_error());

    // Loop: call syscall_reward multiple times and test monotonicity
    uint256_t previous_accumulator = 0;

    auto validator1 = contract.vars.val_execution(val.value().id);

    ASSERT_TRUE(validator1.exists());

    skip_to_next_epoch();

    fmt::println(
        "Initial Balance {} - accumulator: {}",
        intx::to_string(validator1.stake().load().native(), 10),
        intx::to_string(
            validator1.accumulated_reward_per_token().load().native(), 10));

    constexpr size_t NUM_ITERATIONS = 10;
    for (size_t i = 0; i < NUM_ITERATIONS; ++i) {
        EXPECT_FALSE(syscall_reward(val.value().sign_address).has_error());
        auto validator = contract.vars.val_execution(val.value().id);
        auto current_accumulator =
            validator.accumulated_reward_per_token().load().native();
        fmt::println(
            "Iteration {} - accumulator: {}",
            i,
            intx::to_string(current_accumulator, 10));
        fmt::println(
            "curr Balance {}",
            intx::to_string(validator.stake().load().native(), 10));

        // Check that accumulator is monotonically increasing
        ASSERT_GE(current_accumulator, previous_accumulator);

        // Update for next iteration
        previous_accumulator = current_accumulator;
    }

    skip_to_next_epoch();

    auto validator = contract.vars.val_execution(val.value().id);

    ASSERT_TRUE(validator.exists());

    fmt::println(
        "Terminal Balance {} - accumulator: {}",
        intx::to_string(validator.stake().load().native(), 10),
        intx::to_string(
            validator.accumulated_reward_per_token().load().native(), 10));
}

//////////////////////
// Commission Tests //
//////////////////////
TEST_F(Stake, revert_if_commission_too_high)
{
    auto const auth_address = 0xababab_address;
    constexpr auto bad_commission = 2000000000000000000_u256;
    auto const res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, bad_commission);
    EXPECT_EQ(res.assume_error(), StakingError::CommissionTooHigh);

    // add a validator with no commission to set a bad commission
    auto const res2 = add_validator(
        auth_address, MIN_VALIDATE_STAKE, 0 /* starting commission */);
    ASSERT_FALSE(res2.has_error());
    auto const res3 =
        change_commission(res2.value().id, auth_address, bad_commission);
    EXPECT_EQ(res3.assume_error(), StakingError::CommissionTooHigh);
}

TEST_F(Stake, non_auth_attempts_to_change_commission)
{
    // add a validator with no commission. have a random sender try to change
    // the commission.
    auto const auth_address = 0x600d_address;
    auto const bad_sender = 0xbadd_address;

    auto const res = add_validator(
        auth_address, MIN_VALIDATE_STAKE, 0 /* starting commission */);
    ASSERT_FALSE(res.has_error());
    auto const res2 =
        change_commission(res.value().id, bad_sender, 200000000000000000_u256);
    EXPECT_EQ(res2.assume_error(), StakingError::RequiresAuthAddress);
}

class StakeCommission
    : public Stake
    , public ::testing::WithParamInterface<std::tuple<uint64_t, uint256_t>>
{
};

INSTANTIATE_TEST_SUITE_P(
    Rate, StakeCommission,
    ::testing::Combine(
        // commission, expressed as percent
        ::testing::Values(1, 5, 10, 25, 50, 66, 75, 90),
        // variable rewards in MON
        ::testing::Values(
            0, MON / 25, MON / 50, 2 * MON, 10 * MON, 25 * MON, 300 * MON,
            1000 * MON)),
    [](::testing::TestParamInfo<std::tuple<uint64_t, uint256_t>> const &info) {
        return std::to_string(std::get<0>(info.param)) + "_" +
               intx::to_string(std::get<1>(info.param));
    });

TEST_P(StakeCommission, validator_has_commission)
{
    auto const [commission_percent, reward] = GetParam();
    auto const commission = MON * commission_percent / 100;
    auto const auth_address = 0xababab_address;

    auto const val =
        add_validator(auth_address, ACTIVE_VALIDATOR_STAKE, commission);
    EXPECT_FALSE(val.has_error());
    skip_to_next_epoch();
    auto const del_address = 0xaaaabbbb_address;
    EXPECT_FALSE(delegate(val.value().id, del_address, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    skip_to_next_epoch();
    EXPECT_FALSE(syscall_reward(val.value().sign_address, reward).has_error());
    pull_delegator_up_to_date(val.value().id, auth_address);
    pull_delegator_up_to_date(val.value().id, del_address);

    auto const expected_commission = (reward * commission_percent) / 100;
    auto const expected_delegator_reward = (reward - expected_commission) / 2;
    EXPECT_EQ(
        contract.vars.delegator(val.value().id, del_address)
            .rewards()
            .load()
            .native(),
        expected_delegator_reward);
    EXPECT_EQ(
        contract.vars.delegator(val.value().id, auth_address)
            .rewards()
            .load()
            .native(),
        expected_commission + expected_delegator_reward);
}

TEST_F(Stake, validator_changes_commission)
{
    uint256_t const starting_commission = MON / 20; // 5% commission
    auto const auth_address = 0xdeadbeef_address;
    auto const delegator = 0xde1e_address;

    auto const res = add_validator(
        auth_address, ACTIVE_VALIDATOR_STAKE, starting_commission);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    // Create another delegator with 90% of this stake for the validator pool.
    // Otherwise, the auth delegator gets all the commission and this doesn't
    // test anything.
    EXPECT_FALSE(
        delegate(val.id, delegator, 9 * ACTIVE_VALIDATOR_STAKE).has_error());

    skip_to_next_epoch();

    // change validator's commission. this won't go live until the next epoch.
    uint256_t const new_commission = MON / 5; // 20%
    EXPECT_FALSE(
        change_commission(val.id, auth_address, new_commission).has_error());

    // reward this epoch, before and after the boundary, to verify both
    // consensus and snapshot views use the starting commission.
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // auth address has 5% commission and 10% of stake pool. Note that stake
    // pool rewards are applied after the commission, so he gets two rewards at
    // 14.5% each.
    //
    // if the auth has stake `S` and commission `C`, both expressed as percents,
    // the reward including commission is: C+S(1−C)
    uint256_t total_rewards = 2 * REWARD;
    uint256_t auth_running_rewards = REWARD * 29 / 100;
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, delegator);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        auth_running_rewards);
    EXPECT_EQ(
        contract.vars.delegator(val.id, delegator).rewards().load().native(),
        total_rewards - auth_running_rewards);

    // next epoch, new commission is live.
    EXPECT_FALSE(
        syscall_on_epoch_change(contract.vars.epoch.load().native() + 1)
            .has_error());

    // reward before and after the boundary again. uses the new commission.
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // auth address has 20% commission and 10% of stake pool. He gets 28%
    // commission per call (see the comment in the first epoch reward), or 56%
    // of one reward for both.
    total_rewards += 2 * REWARD;
    auth_running_rewards += REWARD * 56 / 100;
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, delegator);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        auth_running_rewards);
    EXPECT_EQ(
        contract.vars.delegator(val.id, delegator).rewards().load().native(),
        total_rewards - auth_running_rewards);
}

////////////////////////////
// Input Validation Tests //
////////////////////////////

TEST_F(Stake, add_validator_revert_invalid_input_size)
{
    auto const sender = 0xdeadbeef_address;
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);

    byte_string_view too_short{};
    auto res = contract.precompile_add_validator(too_short, sender, value);
    EXPECT_EQ(res.assume_error(), AbiDecodeError::InputTooShort);

    auto [too_long, _] =
        craft_add_validator_input(sender, MIN_VALIDATE_STAKE, 0);
    too_long.append({0xFF});
    res = contract.precompile_add_validator(too_long, sender, value);
    EXPECT_EQ(res.assume_error(), StakingError::InvalidInput);
}

TEST_F(Stake, add_validator_revert_bad_signature)
{
    auto const [message, good_secp_sig, good_bls_sig, _] =
        craft_add_validator_input_raw(0xababab_address, MIN_VALIDATE_STAKE);
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);

    // bad secp signature
    {
        auto const bad_secp_keys = gen_secp_keypair(bytes32_t{0x2000});
        auto const bad_secp_sig = sign_secp(message, bad_secp_keys.second);

        AbiEncoder encoder;
        encoder.add_bytes(message);
        encoder.add_bytes(to_byte_string_view(bad_secp_sig));
        encoder.add_bytes(good_bls_sig);
        auto const res = contract.precompile_add_validator(
            encoder.encode_final(), 0xdead_address, value);
        EXPECT_EQ(
            res.assume_error(), StakingError::SecpSignatureVerificationFailed);
    }

    // bad bls signature
    {
        auto const bad_bls_keys = gen_bls_keypair(bytes32_t{0x2000});
        auto const bad_bls_sig = sign_bls(message, bad_bls_keys.second);

        AbiEncoder encoder;
        encoder.add_bytes(message);
        encoder.add_bytes(good_secp_sig);
        encoder.add_bytes(to_byte_string_view(bad_bls_sig));
        auto const res = contract.precompile_add_validator(
            encoder.encode_final(), 0xdead_address, value);
        EXPECT_EQ(
            res.assume_error(), StakingError::BlsSignatureVerificationFailed);
    }
}

TEST_F(Stake, add_validator_revert_msg_value_not_signed)
{
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);
    auto const [input, address] =
        craft_add_validator_input(0xababab_address, 2 * MIN_VALIDATE_STAKE);
    auto const res = contract.precompile_add_validator(input, address, value);
    EXPECT_EQ(res.assume_error(), StakingError::InvalidInput);
}

TEST_F(Stake, add_validator_revert_already_exists)
{
    auto const value = intx::be::store<evmc_uint256be>(MIN_VALIDATE_STAKE);
    auto const [input, address] =
        craft_add_validator_input(0xababab_address, MIN_VALIDATE_STAKE);
    EXPECT_FALSE(
        contract.precompile_add_validator(input, address, value).has_error());
    EXPECT_EQ(
        contract.precompile_add_validator(input, address, value).assume_error(),
        StakingError::ValidatorExists);
}

TEST_F(Stake, add_validator_revert_minimum_stake_not_met)
{
    auto const value = intx::be::store<evmc_uint256be>(uint256_t{1});
    auto const [input, address] =
        craft_add_validator_input(0xababab_address, uint256_t{1});
    auto const res = contract.precompile_add_validator(input, address, value);
    EXPECT_EQ(res.assume_error(), StakingError::InsufficientStake);
}

TEST_F(Stake, nonpayable_functions_revert)
{
    // syscalls
    EXPECT_EQ(
        contract.syscall_snapshot({}, 5 * MON).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.syscall_on_epoch_change({}, 5 * MON).assume_error(),
        StakingError::ValueNonZero);

    // precompiles
    evmc_uint256be value = intx::be::store<evmc_uint256be>(5 * MON);
    EXPECT_EQ(
        contract.precompile_undelegate({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_compound({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_withdraw({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_claim_rewards({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_change_commission({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_validator({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_delegator({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_withdrawal_request({}, {}, value)
            .assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_consensus_valset({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_snapshot_valset({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_execution_valset({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_delegations({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_delegators({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
    EXPECT_EQ(
        contract.precompile_get_epoch({}, {}, value).assume_error(),
        StakingError::ValueNonZero);
}

TEST_F(Stake, auth_address_conflicts_with_linked_list)
{
    // empty pointer
    Address empty{};
    EXPECT_TRUE(add_validator(empty, ACTIVE_VALIDATOR_STAKE).has_error());

    // sentinel
    Address sentinel{};
    std::memset(sentinel.bytes, 0xFF, sizeof(Address));
    EXPECT_TRUE(add_validator(sentinel, ACTIVE_VALIDATOR_STAKE).has_error());
}

TEST_F(Stake, linked_list_removal_state_override)
{
    // even though the empty address and the sentinel address are banned during
    // delegate, a user could state override and trigger unreachable code
    // during live execution via eth call.

    contract.vars.epoch.store(10);

    Address sentinel{};
    std::memset(sentinel.bytes, 0xFF, sizeof(Address));

    uint256_t const stake = 500 * MON;

    // state override invalid validator
    auto validator = contract.vars.val_execution(1u);
    validator.address_flags().store(ValExecution::AddressFlags_t{
        .auth_address = sentinel, .flags = ValidatorFlagsOk});
    validator.stake().store(stake);

    // state override that the contract can process this withdrawal
    state.add_to_balance(STAKING_CA, stake);

    // state override the delegator
    auto delegator = contract.vars.delegator(1u, sentinel);
    delegator.stake().store(stake);
    EXPECT_THROW(
        (void)undelegate(1u, sentinel, 1 /* withdrawal id */, stake),
        MonadException);
}

/////////////////////////
// Add Validator Tests //
/////////////////////////

TEST_F(Stake, add_validator_sufficent_balance)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 = add_validator(
        auth_address, ACTIVE_VALIDATOR_STAKE, 0, bytes32_t{0x1000});
    EXPECT_FALSE(val1.has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    auto val2 = add_validator(
        other_address,
        ACTIVE_VALIDATOR_STAKE,
        0 /* commission */,
        bytes32_t{0x1001});
    EXPECT_FALSE(val2.has_error());

    inc_epoch();

    EXPECT_FALSE(syscall_reward(val1.value().sign_address).has_error());
    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 1);

    EXPECT_EQ(contract.vars.val_execution(1).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(contract.vars.val_execution(2).get_flags(), ValidatorFlagsOk);

    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val2.value().sign_address).has_error());

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);

    EXPECT_EQ(contract.vars.val_execution(1).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(contract.vars.val_execution(2).get_flags(), ValidatorFlagsOk);

    EXPECT_EQ(
        contract.vars.this_epoch_view(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(
        contract.vars.this_epoch_view(2).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);

    EXPECT_EQ(
        contract.vars.val_execution(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(2).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(contract.vars.val_execution(1).commission().load().native(), 0);
    EXPECT_EQ(contract.vars.val_execution(2).commission().load().native(), 0);
}

TEST_F(Stake, add_validator_insufficent_balance)
{
    auto const auth_address = 0xdeadbeef_address;

    auto const val1 = add_validator(
        auth_address,
        MIN_VALIDATE_STAKE,
        1 /* commission */,
        bytes32_t{0x1000});
    EXPECT_FALSE(val1.has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());
    auto val2 = add_validator(
        auth_address,
        ACTIVE_VALIDATOR_STAKE - 1,
        2 /* commission */,
        bytes32_t{0x1001});
    EXPECT_FALSE(val2.has_error());

    inc_epoch();

    EXPECT_EQ(
        StakingError::NotInValidatorSet,
        syscall_reward(val1.value().sign_address).assume_error());

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 0);
    EXPECT_EQ(
        contract.vars.val_execution(1).get_flags(), ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(2).get_flags(), ValidatorFlagsStakeTooLow);

    skip_to_next_epoch();

    EXPECT_EQ(
        StakingError::NotInValidatorSet,
        syscall_reward(val2.value().sign_address).assume_error());

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 0);

    EXPECT_EQ(
        contract.vars.val_execution(1).get_flags(), ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(2).get_flags(), ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(1).stake().load().native(),
        MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(2).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE - 1);
    EXPECT_EQ(contract.vars.val_execution(1).commission().load().native(), 1);
    EXPECT_EQ(contract.vars.val_execution(2).commission().load().native(), 2);
}

/////////////////////
// validator tests
/////////////////////

TEST_F(Stake, validator_delegate_before_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_FALSE(val1.has_error());

    EXPECT_FALSE(delegate(val1.value().id, auth_address, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    auto val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_FALSE(val2.has_error());
    EXPECT_FALSE(delegate(val2.value().id, auth_address, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    inc_epoch();
    skip_to_next_epoch();

    // check val info
    EXPECT_EQ(
        contract.vars.val_execution(val1.value().id).get_flags(),
        ValidatorFlagsOk);
    EXPECT_EQ(
        contract.vars.val_execution(val1.value().id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(val2.value().id).get_flags(),
        ValidatorFlagsOk);
    EXPECT_EQ(
        contract.vars.val_execution(val2.value().id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);

    // check del
    check_delegator_c_state(
        val1.value(),
        auth_address,
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE,
        0);
    check_delegator_c_state(
        val2.value(), auth_address, ACTIVE_VALIDATOR_STAKE, 0);
    check_delegator_c_state(val2.value(), other_address, MIN_VALIDATE_STAKE, 0);
}

TEST_F(Stake, validator_undelegate_before_delegator_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const val1 =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    EXPECT_FALSE(val1.has_error());
    EXPECT_FALSE(delegate(val1.value().id, auth_address, MIN_VALIDATE_STAKE)
                     .has_error());
    EXPECT_EQ(
        undelegate(val1.value().id, auth_address, 1, 50).assume_error(),
        StakingError::InsufficientStake);

    EXPECT_FALSE(syscall_snapshot().has_error());
    auto val2 =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_FALSE(val2.has_error());
    EXPECT_FALSE(delegate(val2.value().id, auth_address, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    EXPECT_EQ(
        undelegate(val2.value().id, auth_address, 1, 50).assume_error(),
        StakingError::InsufficientStake);

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(undelegate(val1.value().id, auth_address, 1, 50).has_error());
    EXPECT_FALSE(undelegate(val2.value().id, auth_address, 1, 50).has_error());
}

TEST_F(Stake, validator_compound_before_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(
        delegate(val1.id, auth_address, MIN_VALIDATE_STAKE).has_error());
    EXPECT_FALSE(compound(val1.id, auth_address).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    EXPECT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(compound(val2.id, auth_address).has_error());

    inc_epoch();

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(
        contract.vars.val_execution(val1.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).stake().load().native(),
        MIN_VALIDATE_STAKE + MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).get_flags(), ValidatorFlagsOk);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);

    check_delegator_c_state(
        val1, auth_address, MIN_VALIDATE_STAKE + MIN_VALIDATE_STAKE, 0);
    check_delegator_c_state(val2, auth_address, ACTIVE_VALIDATOR_STAKE, 0);
    check_delegator_c_state(val2, other_address, MIN_VALIDATE_STAKE, 0);
}

TEST_F(Stake, validator_withdrawal_before_active)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(
        delegate(val1.id, auth_address, MIN_VALIDATE_STAKE).has_error());
    EXPECT_EQ(
        withdraw(val1.id, auth_address, withdrawal_id).assume_error(),
        StakingError::UnknownWithdrawalId);

    EXPECT_FALSE(syscall_snapshot().has_error());

    res =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        withdraw(val2.id, auth_address, withdrawal_id).assume_error(),
        StakingError::UnknownWithdrawalId);

    inc_epoch();
    skip_to_next_epoch();

    // check validator info
    // check delegator info
    EXPECT_EQ(
        withdraw(val1.id, auth_address, withdrawal_id).assume_error(),
        StakingError::UnknownWithdrawalId);
    EXPECT_EQ(
        withdraw(val2.id, auth_address, withdrawal_id).assume_error(),
        StakingError::UnknownWithdrawalId);
}

TEST_F(Stake, validator_joins_in_epoch_delay_period)
{
    auto const auth_address = 0xdeadbeef_address;
    EXPECT_FALSE(syscall_snapshot().has_error());
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    inc_epoch();

    // validator should be active
    skip_to_next_epoch();
    ASSERT_EQ(contract.vars.valset_consensus.length(), 1);
    EXPECT_EQ(contract.vars.valset_consensus.get(0).load(), val.id);
}

TEST_F(Stake, validator_undelegates_and_redelegates_in_epoch_delay_period)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    // activate validator
    skip_to_next_epoch();

    // undelegate everything, deactivating him
    EXPECT_FALSE(undelegate(val.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    pull_delegator_up_to_date(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.val_execution(val.id).get_flags(),
        ValidatorFlagWithdrawn | ValidatorFlagsStakeTooLow);
    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_EQ(contract.vars.valset_consensus.length(), 0);

    // redelegate during boundary
    EXPECT_FALSE(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());
    inc_epoch();

    // next epoch, this validator should be reactivated
    skip_to_next_epoch();
    ASSERT_EQ(contract.vars.valset_consensus.length(), 1);
    EXPECT_EQ(contract.vars.valset_consensus.get(0).load(), val.id);
}

TEST_F(Stake, validator_activation_via_delegate)
{
    auto const auth_address = 0xdeadbeef_address;

    // create, minimum amount of stake to be a validator, but less than the
    // amount required to be put in the valset.
    auto const res = add_validator(auth_address, MIN_VALIDATE_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_EQ(
        contract.vars.val_execution(val.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    skip_to_next_epoch();
    EXPECT_TRUE(contract.vars.this_epoch_valset().empty());

    // a delegator stakes enough to activate the validator
    EXPECT_FALSE(
        delegate(val.id, 0xabab_address, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        contract.vars.val_execution(val.id).get_flags(), ValidatorFlagsOk);
    skip_to_next_epoch();
    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 1);

    // undelegate, once again deactivating this validator
    EXPECT_FALSE(undelegate(val.id, 0xabab_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    EXPECT_EQ(
        contract.vars.val_execution(val.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    skip_to_next_epoch();
    EXPECT_TRUE(contract.vars.this_epoch_valset().empty());
}

TEST_F(Stake, validator_multiple_delegations)
{ // epoch 1
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    // epoch 2
    skip_to_next_epoch();
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, REWARD);

    for (uint32_t i = 0; i < 1; ++i) {
        EXPECT_FALSE(
            delegate(val.id, auth_address, MIN_VALIDATE_STAKE).has_error());
    }

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, 2 * REWARD);
    EXPECT_FALSE(
        delegate(val.id, auth_address, MIN_VALIDATE_STAKE).has_error());

    // epoch 3
    inc_epoch();

    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE,
        2 * REWARD);
    // epoch 4
    skip_to_next_epoch();
    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + 2 * MIN_VALIDATE_STAKE,
        2 * REWARD);
}

// compound a validator before and after snapshot
TEST_F(Stake, validator_compound)
{ // epoch 1
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    // epoch 2
    skip_to_next_epoch();
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, REWARD);

    for (uint32_t i = 0; i < 1; ++i) {
        EXPECT_FALSE(compound(val.id, auth_address).has_error());
    }

    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    check_delegator_c_state(val, auth_address, ACTIVE_VALIDATOR_STAKE, REWARD);

    EXPECT_FALSE(compound(val.id, auth_address).has_error());

    // epoch 3
    inc_epoch();

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + REWARD, 0);
    // epoch 4
    skip_to_next_epoch();
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + 2 * REWARD, 0);
}

TEST_F(Stake, validator_undelegate)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(
        delegate(val1.id, auth_address, MIN_VALIDATE_STAKE).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(
        undelegate(val1.id, auth_address, 1, MIN_VALIDATE_STAKE).has_error());
    EXPECT_FALSE(
        undelegate(val1.id, auth_address, 2, MIN_VALIDATE_STAKE).has_error());
    EXPECT_FALSE(
        undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE / 2)
            .has_error());
    EXPECT_FALSE(
        undelegate(val2.id, auth_address, 2, ACTIVE_VALIDATOR_STAKE / 2)
            .has_error());
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).get_flags(),
        ValidatorFlagWithdrawn | ValidatorFlagsStakeTooLow);

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(withdraw(val1.id, auth_address, withdrawal_id).has_error());
    EXPECT_FALSE(withdraw(val2.id, auth_address, withdrawal_id).has_error());

    // check val info
    EXPECT_EQ(
        contract.vars.val_execution(val1.id).get_flags(),
        ValidatorFlagWithdrawn | ValidatorFlagsStakeTooLow);
    EXPECT_EQ(contract.vars.val_execution(val1.id).stake().load().native(), 0);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).get_flags(),
        ValidatorFlagsStakeTooLow);
    EXPECT_EQ(
        contract.vars.val_execution(val2.id).stake().load().native(),
        MIN_VALIDATE_STAKE);

    // check del
    check_delegator_c_state(val1, auth_address, 0, 0);
    check_delegator_c_state(val2, auth_address, 0, 0);
    check_delegator_c_state(val2, other_address, MIN_VALIDATE_STAKE, 0);
}

TEST_F(Stake, validator_exit_via_validator)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(undelegate(
                     val1.id,
                     auth_address,
                     1,
                     ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE - 1)
                     .has_error());
    EXPECT_FALSE(
        undelegate(val2.id, other_address, 1, MIN_VALIDATE_STAKE).has_error());

    EXPECT_FALSE(delegate(
                     val1.id,
                     auth_address,
                     ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE - 1)
                     .has_error());

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 1);

    EXPECT_FALSE(
        delegate(val2.id, other_address, MIN_VALIDATE_STAKE).has_error());

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);
    skip_to_next_epoch();

    EXPECT_FALSE(withdraw(val1.id, auth_address, withdrawal_id).has_error());
    EXPECT_FALSE(withdraw(val2.id, other_address, withdrawal_id).has_error());
}

TEST_F(Stake, validator_exit_via_delegator)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    uint8_t const withdrawal_id{1};

    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    EXPECT_FALSE(undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    EXPECT_FALSE(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 1);

    EXPECT_FALSE(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);
    skip_to_next_epoch();

    EXPECT_FALSE(withdraw(val1.id, auth_address, withdrawal_id).has_error());
    EXPECT_FALSE(withdraw(val2.id, auth_address, withdrawal_id).has_error());
}

TEST_F(Stake, validator_exit_multiple_delegations)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    EXPECT_EQ(get_balance(auth_address), 0);

    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    EXPECT_FALSE(delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    EXPECT_FALSE(delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    inc_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);

    EXPECT_FALSE(undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    EXPECT_FALSE(undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    EXPECT_FALSE(syscall_reward(val1.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val2.sign_address).has_error());

    EXPECT_FALSE(delegate(
                     val1.id,
                     auth_address,
                     ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1)
                     .has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(delegate(
                     val2.id,
                     auth_address,
                     ACTIVE_VALIDATOR_STAKE - MIN_VALIDATE_STAKE - 1)
                     .has_error());

    inc_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 0);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(claim_rewards(val2.id, auth_address).has_error());
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(withdraw(val2.id, auth_address, 1).has_error());
    EXPECT_EQ(
        get_balance(auth_address), ACTIVE_VALIDATOR_STAKE + 996015936254980079);

    EXPECT_FALSE(claim_rewards(val2.id, other_address).has_error());
    EXPECT_EQ(get_balance(other_address), 3984063745019920);

    EXPECT_FALSE(claim_rewards(val1.id, auth_address).has_error());
    EXPECT_FALSE(withdraw(val1.id, auth_address, 1).has_error());
    EXPECT_EQ(
        get_balance(auth_address),
        ACTIVE_VALIDATOR_STAKE + (REWARD - 1) + ACTIVE_VALIDATOR_STAKE +
            996015936254980079);
}

TEST_F(Stake, validator_exit_multiple_delegations_full_withdrawal)
{
    constexpr auto smaller_stake = 1'000'000 * MON;
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    EXPECT_EQ(get_balance(auth_address), 0);

    auto res = add_validator(auth_address, smaller_stake, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    EXPECT_FALSE(delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res = add_validator(other_address, smaller_stake, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    EXPECT_FALSE(delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE / 2)
                     .has_error());

    inc_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);

    EXPECT_FALSE(undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    EXPECT_FALSE(syscall_reward(val1.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val2.sign_address).has_error());

    EXPECT_FALSE(undelegate(val2.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    EXPECT_FALSE(
        delegate(
            val1.id, auth_address, ACTIVE_VALIDATOR_STAKE - smaller_stake - 1)
            .has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(
        delegate(
            val2.id, auth_address, ACTIVE_VALIDATOR_STAKE - smaller_stake - 1)
            .has_error());

    inc_epoch();
    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 0);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(claim_rewards(val2.id, auth_address).has_error());
    EXPECT_FALSE(withdraw(val2.id, auth_address, 1).has_error());
    EXPECT_EQ(
        get_balance(auth_address), ACTIVE_VALIDATOR_STAKE + 961538461538461538);

    EXPECT_FALSE(claim_rewards(val2.id, other_address).has_error());
    EXPECT_EQ(get_balance(other_address), 38461538461538461);

    EXPECT_FALSE(claim_rewards(val1.id, auth_address).has_error());
    EXPECT_FALSE(withdraw(val1.id, auth_address, 1).has_error());
    EXPECT_EQ(
        get_balance(auth_address),
        ACTIVE_VALIDATOR_STAKE + (REWARD - 1) + ACTIVE_VALIDATOR_STAKE +
            961538461538461538);

    check_delegator_c_state(val1, auth_address, ACTIVE_VALIDATOR_STAKE - 1, 0);
    check_delegator_c_state(
        val2, auth_address, ACTIVE_VALIDATOR_STAKE - smaller_stake - 1, 0);
    check_delegator_c_state(val2, other_address, smaller_stake, 0);

    EXPECT_FALSE(
        undelegate(val1.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE - 1)
            .has_error());

    EXPECT_FALSE(undelegate(
                     val2.id,
                     auth_address,
                     1,
                     ACTIVE_VALIDATOR_STAKE - smaller_stake - 1)
                     .has_error());

    skip_to_next_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(claim_rewards(val2.id, auth_address).has_error());
    EXPECT_FALSE(withdraw(val2.id, auth_address, 1).has_error());

    EXPECT_FALSE(claim_rewards(val2.id, other_address).has_error());
    EXPECT_EQ(get_balance(other_address), 38461538461538461);

    EXPECT_FALSE(claim_rewards(val1.id, auth_address).has_error());
    EXPECT_FALSE(withdraw(val1.id, auth_address, 1).has_error());
    EXPECT_EQ(
        get_balance(auth_address),
        ACTIVE_VALIDATOR_STAKE + (REWARD - 1) + ACTIVE_VALIDATOR_STAKE +
            961538461538461538 + ACTIVE_VALIDATOR_STAKE - 1 +
            ACTIVE_VALIDATOR_STAKE - smaller_stake - 1);
}

TEST_F(Stake, validator_exit_claim_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    constexpr auto smaller_stake = 1'000'000 * MON;
    constexpr auto larger_stake = 50'000'000 * MON;
    auto res = add_validator(auth_address, smaller_stake, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(delegate(val1.id, auth_address, larger_stake).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res = add_validator(other_address, smaller_stake, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(delegate(val2.id, auth_address, larger_stake).has_error());

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val1.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val2.sign_address).has_error());

    EXPECT_FALSE(
        undelegate(val1.id, auth_address, 1, larger_stake).has_error());
    EXPECT_FALSE(
        undelegate(val2.id, auth_address, 1, larger_stake).has_error());

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 0);

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(claim_rewards(val1.id, auth_address).has_error());
    EXPECT_EQ(get_balance(auth_address), REWARD - 1);
    EXPECT_FALSE(claim_rewards(val2.id, auth_address).has_error());
    EXPECT_EQ(get_balance(auth_address), 980392156862745098 + (REWARD - 1));

    EXPECT_EQ(get_balance(other_address), 0);
    EXPECT_FALSE(claim_rewards(val2.id, other_address).has_error());
    EXPECT_EQ(get_balance(other_address), 19607843137254901);
}

TEST_F(Stake, validator_exit_compound)
{
    constexpr auto smaller_stake = 1'000'000 * MON;
    constexpr auto larger_stake = 50'000'000 * MON;
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;
    auto const reward = 60 * MON;

    auto res = add_validator(auth_address, smaller_stake, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(delegate(val1.id, auth_address, larger_stake).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res = add_validator(other_address, smaller_stake, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(delegate(val2.id, auth_address, larger_stake).has_error());

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val1.sign_address, reward).has_error());
    EXPECT_FALSE(syscall_reward(val2.sign_address, reward).has_error());

    EXPECT_FALSE(compound(val1.id, auth_address).has_error());
    EXPECT_FALSE(compound(val2.id, auth_address).has_error());
    EXPECT_FALSE(compound(val2.id, other_address).has_error());

    EXPECT_FALSE(
        undelegate(val1.id, auth_address, 1, larger_stake).has_error());
    EXPECT_FALSE(
        undelegate(val2.id, auth_address, 1, larger_stake).has_error());

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 0);
    EXPECT_FALSE(claim_rewards(val1.id, auth_address).has_error());
    EXPECT_FALSE(claim_rewards(val2.id, auth_address).has_error());
    EXPECT_FALSE(claim_rewards(val2.id, other_address).has_error());

    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_EQ(get_balance(other_address), 0);

    constexpr uint256_t expected_reward1 =
        1176470588235294117_u256; // 1/51 of the reward
    constexpr uint256_t expected_reward2 =
        58823529411764705882_u256; // 50/51 of the reward
    EXPECT_LE(expected_reward1 + expected_reward2, reward);
    check_delegator_c_state(
        val2,
        other_address,
        smaller_stake + expected_reward1,
        0); // didn't undelegate

    check_delegator_c_state(
        val2, auth_address, expected_reward2, 0); // undelegated

    check_delegator_c_state(val1, auth_address, smaller_stake + reward - 1, 0);
}

TEST_F(Stake, validator_removes_self)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, MIN_VALIDATE_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_FALSE(
        delegate(val.id, 0xabab_address, ACTIVE_VALIDATOR_STAKE).has_error());
    skip_to_next_epoch();

    uint8_t withdrawal_id{1};
    EXPECT_FALSE(
        undelegate(val.id, auth_address, withdrawal_id, MIN_VALIDATE_STAKE)
            .has_error());

    // check execution state
    auto val_execution = contract.vars.val_execution(val.id);
    EXPECT_EQ(val_execution.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
    // despite having enough stake to be active, the primary validator has
    // withdrawn, rendering the validator inactive
    EXPECT_TRUE(val_execution.get_flags() & ValidatorFlagWithdrawn);

    // validator can still be rewarded this epoch because he's active
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // take snapshot
    EXPECT_FALSE(syscall_snapshot().has_error());

    // execution view and consensus view should both show validator removed
    EXPECT_EQ(contract.vars.valset_consensus.length(), 0);
    // validate snapshot view since the current epoch is ongoing.
    EXPECT_EQ(contract.vars.valset_snapshot.length(), 1);
    EXPECT_EQ(
        contract.vars.snapshot_view(val.id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE + MIN_VALIDATE_STAKE);

    // rewards now reference the snapshot set and should continue to work
    // for this validator
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    inc_epoch();

    // consensus view doesn't include this validator, and reward fails
    EXPECT_EQ(
        syscall_reward(val.sign_address).assume_error(),
        StakingError::NotInValidatorSet);
}

TEST_F(Stake, two_validators_remove_self)
{
    auto compare_sets = [](StorageArray<u64_be> &state_valset,
                           std::vector<u64_be> &expected_valset) {
        EXPECT_EQ(state_valset.length(), expected_valset.size());
        for (uint64_t i = 0; i < state_valset.length(); ++i) {
            u64_be const val_id = state_valset.get(i).load();
            EXPECT_TRUE(std::ranges::contains(expected_valset, val_id));
        }
    };

    std::vector<u64_be> expected_full_valset;
    auto const auth_address = 0xdeadbeef_address;

    for (uint32_t i = 0; i < 13; ++i) {
        auto const res = add_validator(
            auth_address,
            ACTIVE_VALIDATOR_STAKE,
            0 /* commission */,
            bytes32_t{i + 1});
        ASSERT_FALSE(res.has_error());
        expected_full_valset.push_back(res.value().id);
    }

    compare_sets(contract.vars.valset_execution, expected_full_valset);
    skip_to_next_epoch();
    compare_sets(contract.vars.valset_consensus, expected_full_valset);

    // remove validator 9 and validator 4
    auto expected_valset_with_undelegations = expected_full_valset;
    expected_valset_with_undelegations.erase(
        expected_valset_with_undelegations.begin() + 9);
    expected_valset_with_undelegations.erase(
        expected_valset_with_undelegations.begin() + 4);
    EXPECT_FALSE(
        undelegate(
            expected_full_valset[9], auth_address, 1, ACTIVE_VALIDATOR_STAKE)
            .has_error());
    EXPECT_FALSE(
        undelegate(
            expected_full_valset[4], auth_address, 1, ACTIVE_VALIDATOR_STAKE)
            .has_error());

    skip_to_next_epoch();
    compare_sets(
        contract.vars.valset_execution, expected_valset_with_undelegations);
    compare_sets(
        contract.vars.valset_consensus, expected_valset_with_undelegations);

    EXPECT_FALSE(
        delegate(expected_full_valset[4], auth_address, ACTIVE_VALIDATOR_STAKE)
            .has_error());
    EXPECT_FALSE(
        delegate(expected_full_valset[9], auth_address, ACTIVE_VALIDATOR_STAKE)
            .has_error());
    compare_sets(contract.vars.valset_execution, expected_full_valset);
    skip_to_next_epoch();
    compare_sets(contract.vars.valset_consensus, expected_full_valset);
}

TEST_F(Stake, validator_constant_validator_set)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();

    EXPECT_FALSE(
        delegate(val1.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    res =
        add_validator(other_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1001});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.value();

    EXPECT_FALSE(
        delegate(val2.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    uint8_t withdrawal_id{1};

    for (int i = 0; i < 10; ++i) {
        EXPECT_FALSE(
            undelegate(
                val1.id, auth_address, withdrawal_id, MIN_VALIDATE_STAKE + 1)
                .has_error());

        EXPECT_FALSE(
            undelegate(
                val2.id, auth_address, withdrawal_id, MIN_VALIDATE_STAKE + 1)
                .has_error());

        EXPECT_FALSE(delegate(val1.id, auth_address, MIN_VALIDATE_STAKE + 1)
                         .has_error());

        EXPECT_FALSE(delegate(val2.id, auth_address, MIN_VALIDATE_STAKE + 1)
                         .has_error());

        ++withdrawal_id;
    }

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);

    skip_to_next_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 2);
}

TEST_F(Stake, validator_joining_boundary_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto res = add_validator(
        auth_address,
        ACTIVE_VALIDATOR_STAKE,
        0 /* commission */,
        bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.value();
    ValResult val2{};

    // add a new validator before adding the snapshot. simulate the case
    // when a malicous consensus client rewards themselves early. all other
    // nodes will not reward him, indicated by the BLOCK_AUTHOR_NOT_IN_SET
    // error code, producing a state root mismatch on that block.
    EXPECT_FALSE(syscall_snapshot().has_error());
    unsigned DELAY_WINDOW = 6000;
    for (unsigned i = 0; i < DELAY_WINDOW; ++i) {
        EXPECT_EQ(
            StakingError::NotInValidatorSet,
            syscall_reward(val1.sign_address).assume_error());

        if (i == (DELAY_WINDOW - 100)) {
            res = add_validator(
                auth_address,
                ACTIVE_VALIDATOR_STAKE,
                0 /* commission */,
                bytes32_t{0x1001});
            ASSERT_FALSE(res.has_error());
            val2 = res.value();
        }
    }

    // joined after the boundary, not active
    EXPECT_EQ(
        StakingError::NotInValidatorSet,
        syscall_reward(val2.sign_address).assume_error());
    inc_epoch();

    // joined before the boundary, now active
    EXPECT_FALSE(syscall_reward(val1.sign_address).has_error());
}

// consensus misses a snapshot, validator cant join
TEST_F(Stake, validator_miss_snapshot_miss_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(
        auth_address,
        ACTIVE_VALIDATOR_STAKE,
        0 /* commission */,
        bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());

    inc_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 0);
    EXPECT_EQ(contract.vars.val_execution(1).get_flags(), ValidatorFlagsOk);

    EXPECT_EQ(
        contract.vars.val_execution(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(contract.vars.val_execution(1).commission().load().native(), 0);
}

// consensus misses a snapshot, validator cant leave
TEST_F(Stake, validator_miss_snapshot_miss_deactivation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    skip_to_next_epoch();

    EXPECT_FALSE(undelegate(val.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    inc_epoch();

    EXPECT_EQ(contract.vars.this_epoch_valset().length(), 1);
    EXPECT_EQ(
        contract.vars.val_execution(1).get_flags(),
        ValidatorFlagWithdrawn | ValidatorFlagsStakeTooLow);

    EXPECT_EQ(
        contract.vars.this_epoch_view(1).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(contract.vars.val_execution(1).stake().load().native(), 0);
}

TEST_F(Stake, validator_external_rewards_failure_conditions)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_EQ(
        external_reward(val.id, auth_address, 20 * MON).assume_error(),
        StakingError::NotInValidatorSet);
    skip_to_next_epoch(); // validator in set

    EXPECT_EQ(
        external_reward(20 /* val id */, auth_address, 20 * MON).assume_error(),
        StakingError::UnknownValidator);

    EXPECT_EQ(
        external_reward(val.id, auth_address, 5).assume_error(),
        StakingError::ExternalRewardTooSmall);
    EXPECT_EQ(
        external_reward(val.id, auth_address, MIN_EXTERNAL_REWARD - 1)
            .assume_error(),
        StakingError::ExternalRewardTooSmall);

    EXPECT_EQ(
        external_reward(val.id, auth_address, MAX_EXTERNAL_REWARD + 1)
            .assume_error(),
        StakingError::ExternalRewardTooLarge);

    EXPECT_FALSE(external_reward(val.id, auth_address, 20 * MON).has_error());
}

TEST_F(Stake, validator_external_rewards_uniform_reward_pool)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    std::array<Address, 5> delegators = {
        auth_address,
        0xaaaa_address,
        0xbbbb_address,
        0xcccc_address,
        0xdddd_address};
    for (auto const &d : delegators) {
        if (d != auth_address) {
            EXPECT_FALSE(
                delegate(val.id, d, ACTIVE_VALIDATOR_STAKE).has_error());
        }
    }
    skip_to_next_epoch(); // validator in set, all delegators active.

    // external reward distributed uniformly
    EXPECT_FALSE(external_reward(val.id, auth_address, 20 * MON).has_error());
    for (auto const &d : delegators) {
        pull_delegator_up_to_date(val.id, d);
        EXPECT_EQ(
            contract.vars.delegator(val.id, d).rewards().load().native(),
            4 * MON);
    }
}

/////////////////////
// delegate tests
/////////////////////

TEST_F(Stake, delegator_none_init)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const delegator = 1337_address;

    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    // 1. call get_delegator_info()
    check_delegator_zero(val.id, delegator);

    // 2. undelegate
    EXPECT_EQ(
        undelegate(val.id, delegator, 1, 100).assume_error(),
        StakingError::InsufficientStake);
    check_delegator_zero(val.id, delegator);

    EXPECT_FALSE(undelegate(val.id, delegator, 1, 0).has_error());
    check_delegator_zero(val.id, delegator);

    // 3. withdraw
    EXPECT_EQ(
        withdraw(val.id, delegator, 1).assume_error(),
        StakingError::UnknownWithdrawalId);
    check_delegator_zero(val.id, delegator);

    // 4. compound
    EXPECT_FALSE(compound(val.id, delegator).has_error());
    check_delegator_zero(val.id, delegator);

    // 5. claim
    EXPECT_FALSE(claim_rewards(val.id, delegator).has_error());
    check_delegator_zero(val.id, delegator);
    EXPECT_EQ(get_balance(delegator), 0);
}

TEST_F(Stake, random_delegator_not_allocated_state)
{
    auto const auth_address = 0xdeadbeef_address;

    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // state should not be allocated
    check_delegator_zero(val.id, 0xaaaabbbb_address);
}

TEST_F(Stake, delegator_state_cleared_after_withdraw)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const delegator = 1337_address;

    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_FALSE(
        delegate(val.id, delegator, ACTIVE_VALIDATOR_STAKE).has_error());

    skip_to_next_epoch();

    // this causes del.acc to be nonzero
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    skip_to_next_epoch();

    // clear rewards slot
    EXPECT_FALSE(claim_rewards(val.id, delegator).has_error());
    // remove stake, setting del.acc to zero.
    EXPECT_FALSE(
        undelegate(val.id, delegator, 1, ACTIVE_VALIDATOR_STAKE).has_error());

    // state should be deallocated
    check_delegator_zero(val.id, delegator);

    // just to be sure, let's redelegate again
    EXPECT_FALSE(
        delegate(val.id, delegator, ACTIVE_VALIDATOR_STAKE).has_error());
    skip_to_next_epoch();
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    pull_delegator_up_to_date(val.id, delegator);
    pull_delegator_up_to_date(val.id, auth_address);

    // check stake and rewards make sense
    auto del = contract.vars.delegator(val.id, delegator);
    EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
    EXPECT_GT(del.rewards().load().native(), 0);
    EXPECT_GT(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        del.rewards().load().native());
}

TEST_F(Stake, delegate_noop_add_zero_stake)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    auto const d0 = 0xaaaabbbb_address;
    EXPECT_FALSE(delegate(val.id, d0, 0).has_error());

    skip_to_next_epoch();
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD);
}

TEST_F(Stake, delegate_noop_subsequent_zero_stake)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const d0 = 0xaaaabbbb_address;

    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        2 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    skip_to_next_epoch();

    // reward the validator.
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // validator should receive all the reward being the only active
    // delegator.
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD + REWARD / 2);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD + REWARD / 2);

    EXPECT_FALSE(delegate(val.id, d0, 0).has_error());

    ASSERT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(delegate(val.id, d0, 0).has_error());

    {
        auto del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.rewards().load().native(), REWARD + REWARD / 2);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

TEST_F(Stake, delegate_revert_unknown_validator)
{
    auto const d0 = 0xaaaabbbb_address;
    EXPECT_EQ(
        delegate(3, d0, ACTIVE_VALIDATOR_STAKE).assume_error(),
        StakingError::UnknownValidator);
}

TEST_F(Stake, delegate_init)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    ASSERT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());
    inc_epoch();

    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        REWARD / 3);

    {
        auto del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

TEST_F(Stake, delegate_redelegate_before_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const other_address = 0xdeaddead_address;

    auto const res = add_validator(
        auth_address, ACTIVE_VALIDATOR_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(2, val.id)
            .load()
            .refcount.native(),
        1);

    EXPECT_FALSE(
        delegate(val.id, other_address, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(2, val.id)
            .load()
            .refcount.native(),
        2);

    EXPECT_FALSE(
        delegate(val.id, other_address, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(2, val.id)
            .load()
            .refcount.native(),
        2);

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(
        delegate(val.id, other_address, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(3, val.id)
            .load()
            .refcount.native(),
        1);

    EXPECT_FALSE(
        delegate(val.id, other_address, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(3, val.id)
            .load()
            .refcount.native(),
        1);

    inc_epoch();

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    pull_delegator_up_to_date(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(2, val.id)
            .load()
            .refcount.native(),
        1);

    pull_delegator_up_to_date(val.id, other_address);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(2, val.id)
            .load()
            .refcount.native(),
        0);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, other_address)
            .rewards()
            .load()
            .native(),
        2 * REWARD / 3);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(2, val.id)
            .load()
            .refcount.native(),
        0);

    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, other_address);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 3 + REWARD / 5);
    EXPECT_EQ(
        contract.vars.delegator(val.id, other_address)
            .rewards()
            .load()
            .native(),
        2 * REWARD / 3 + (4 * REWARD / 5));

    EXPECT_FALSE(contract.vars.accumulated_reward_per_token(2, val.id)
                     .load_checked()
                     .has_value());
    EXPECT_FALSE(contract.vars.accumulated_reward_per_token(3, val.id)
                     .load_checked()
                     .has_value());
}

TEST_F(Stake, delegate_redelegate_after_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE / 2).has_error());
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE / 2).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE / 2).has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE / 2).has_error());

    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    // reward the validator.
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        0);
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    auto acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    auto acc_boundary =
        contract.vars.accumulated_reward_per_token(4, val.id).load();
    EXPECT_EQ(acc_boundary.value.native(), 0);
    EXPECT_EQ(acc_boundary.refcount.native(), 1);

    inc_epoch();

    // validator should receive all the reward being the only active
    // delegator.
    pull_delegator_up_to_date(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3);

    // calling touch again should be a no-op
    pull_delegator_up_to_date(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3);

    // secondary delegators were not active and should receive nothing.
    EXPECT_EQ(contract.vars.delegator(val.id, d0).rewards().load().native(), 0);
    EXPECT_EQ(contract.vars.delegator(val.id, d1).rewards().load().native(), 0);

    // reward again with only 1 active delegator
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3 + REWARD / 2);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 2);
    EXPECT_EQ(contract.vars.delegator(val.id, d1).rewards().load().native(), 0);

    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3 + REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        REWARD / 3);

    acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc_boundary = contract.vars.accumulated_reward_per_token(4, val.id).load();
    EXPECT_EQ(acc_boundary.value.native(), 0);
    EXPECT_EQ(acc_boundary.refcount.native(), 0);

    {
        auto del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

TEST_F(Stake, delegate_undelegate_withdraw_redelegate)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    // reward the validator.

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    inc_epoch();

    // reward again with only 1 active delegator
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * 3 + REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        REWARD / 2 + REWARD / 3);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        REWARD / 3);

    auto acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    auto acc_boundary =
        contract.vars.accumulated_reward_per_token(4, val.id).load();
    EXPECT_EQ(acc_boundary.value.native(), 0);
    EXPECT_EQ(acc_boundary.refcount.native(), 0);

    uint8_t const withdrawal_id{1};
    EXPECT_FALSE(undelegate(val.id, d0, withdrawal_id, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(undelegate(val.id, d1, withdrawal_id, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    inc_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(withdraw(val.id, d0, withdrawal_id).has_error());
    EXPECT_FALSE(withdraw(val.id, d1, withdrawal_id).has_error());

    {
        auto del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    {
        auto del = contract.vars.delegator(val.id, d0);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 8);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    {
        auto del = contract.vars.delegator(val.id, d1);

        EXPECT_EQ(del.stake().load().native(), 0);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(
            del.next_delta_stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 9);
    }
}

TEST_F(Stake, delegator_delegates_in_epoch_delay_period)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    skip_to_next_epoch();

    auto const del_address = 0xaaaabbbb_address;
    EXPECT_FALSE(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE).has_error());

    // take snapshot and reward during the window. delegator *should not*
    // receive rewards.
    EXPECT_FALSE(syscall_snapshot().has_error());
    unsigned DELAY_WINDOW = 6000;

    for (unsigned i = 0; i < DELAY_WINDOW; ++i) {
        EXPECT_EQ(
            contract.vars.this_epoch_view(val.id).stake().load().native(),
            ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(
            contract.vars.val_execution(val.id).stake().load().native(),
            ACTIVE_VALIDATOR_STAKE * 2);
        EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    }

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, del_address);

    // validator should get all the rewards since the secondary delegator
    // does not become active in the consensus view until after the window
    // expires.
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD * DELAY_WINDOW);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).rewards().load().native(),
        0);
}

TEST_F(Stake, delegate_redelegation_refcount_before_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    // do a bunch of redelegations before snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_FALSE(delegate(val.id, auth_address, MON).has_error());
    }

    EXPECT_FALSE(syscall_snapshot().has_error());

    // and some more in the snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_FALSE(delegate(val.id, auth_address, MON).has_error());
    }
    inc_epoch();

    auto acc = contract.vars.accumulated_reward_per_token(2, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    pull_delegator_up_to_date(val.id, auth_address);

    acc = contract.vars.accumulated_reward_per_token(2, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    EXPECT_FALSE(syscall_snapshot().has_error());
    inc_epoch();

    pull_delegator_up_to_date(val.id, auth_address);

    acc = contract.vars.accumulated_reward_per_token(2, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);
}

TEST_F(Stake, delegate_redelegation_refcount_after_activation)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_FALSE(syscall_snapshot().has_error());
    inc_epoch();

    // do a bunch of redelegations before snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_FALSE(delegate(val.id, auth_address, MON).has_error());
    }

    EXPECT_FALSE(syscall_snapshot().has_error());

    // and some more in the snapshot
    for (int i = 0; i < 20; ++i) {
        EXPECT_FALSE(delegate(val.id, auth_address, MON).has_error());
    }

    auto acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    acc = contract.vars.accumulated_reward_per_token(4, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    inc_epoch();

    pull_delegator_up_to_date(val.id, auth_address);

    acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.accumulated_reward_per_token(4, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 1);

    EXPECT_FALSE(syscall_snapshot().has_error());
    inc_epoch();

    pull_delegator_up_to_date(val.id, auth_address);

    acc = contract.vars.accumulated_reward_per_token(3, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);

    acc = contract.vars.accumulated_reward_per_token(4, val.id).load();
    EXPECT_EQ(acc.value.native(), 0);
    EXPECT_EQ(acc.refcount.native(), 0);
}

// There are 3 cases for the historic accumulator when a delegator joins a
// validator's stake pool.
// 1. delegators join in same snapshot window as validator
// 2. delegator join in different snapshot window as validator and acc is
// zero
// 3. delegator join in different snapshot window as validator and acc is
// non zero
TEST_F(Stake, delegator_epoch_accumulator_same_snapshot)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    // add 2 delegators in same snapshot window
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());
    inc_epoch();

    // 3 delegators become active. Therefore ref count should be 3 and acc
    // is 0
    EXPECT_EQ(
        0,
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .value.native());
    EXPECT_EQ(
        3,
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .refcount.native());

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    // acc and ref should be empty now
    EXPECT_EQ(
        0,
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .value.native());
    EXPECT_EQ(
        0,
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .refcount.native());
}

TEST_F(Stake, delegator_epoch_accumulator_diff_snapshot)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_FALSE(syscall_snapshot().has_error());
    // add 2 delegators in different snapshot window
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    inc_epoch();

    // 1 delegators become active. Therefore ref count should be 1 and acc
    // is 0
    EXPECT_EQ(
        0,
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .value.native());
    EXPECT_EQ(
        1,
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .refcount.native());

    EXPECT_FALSE(syscall_snapshot().has_error());
    inc_epoch();

    // 2 delegators become active. Therefore ref count should be 2 and acc
    // is 0 since no rewards
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .value.native(),
        0);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .refcount.native(),
        2);

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    // acc and ref should be empty now for both epochs
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .value.native(),
        0);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .refcount.native(),
        0);

    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .value.native(),
        0);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .refcount.native(),
        0);
}

TEST_F(Stake, delegator_epoch_nz_accumulator_diff_snapshot)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_FALSE(syscall_snapshot().has_error());

    // add 2 delegators in different snapshot window
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    inc_epoch();

    // 1 delegators become active. Therefore ref count should be 1 and acc
    // is 0
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .value.native(),
        0);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .refcount.native(),
        1);

    // validator is rewarded. next acc is nonzero.
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());
    inc_epoch();

    // 2 delegators become active. Therefore ref count should be 2 and acc
    // is nonzero
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .value.native(),
        (REWARD * UNIT_BIAS) / ACTIVE_VALIDATOR_STAKE);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .refcount.native(),
        2);

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    // acc and ref should be empty now for both epochs
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .value.native(),
        0);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{2}, val.id)
            .load()
            .refcount.native(),
        0);

    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .value.native(),
        0);
    EXPECT_EQ(
        contract.vars.accumulated_reward_per_token(u64_be{3}, val.id)
            .load()
            .refcount.native(),
        0);
    {
        auto del = contract.vars.delegator(val.id, d0);
        EXPECT_GT(del.accumulated_reward_per_token().load().native(), 0);
    }
}

TEST_F(Stake, validator_exit_delegator_boundary_nz_accumulator)
{
    // Scenario:
    // Add a validator in epoch N. Validator is active in epoch N+1.  During the
    // the boundary between N+1 and N+2, add a delegator. Ensure the delegator's
    // accumulator is set correctly. This is an edge case because the validator
    // will be out of the set in N+2 and will therefore not push his
    // accumulator.
    auto const auth_address = 0xdeadbeef_address;
    auto del = 0xaaaabbbb_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    skip_to_next_epoch();
    // reward validator so his accumulator is nonzero
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(undelegate(val.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    // add delegator in the boundary
    // he greedily sets his future accumulator to val.acc
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(delegate(val.id, del, ACTIVE_VALIDATOR_STAKE).has_error());

    // reward the validator in the boundary, so the greedy accumulator for N+2
    // is now stale.
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // goto epoch N+1. delegator is not active until N+2
    inc_epoch();

    EXPECT_TRUE(contract.vars.valset_execution.empty());
    check_delegator_c_state(val, del, 0, 0);

    // goto epoch N+2
    skip_to_next_epoch();

    // load accumulators
    auto const epoch_acc =
        contract.vars
            .accumulated_reward_per_token(contract.vars.epoch.load(), val.id)
            .load();
    EXPECT_EQ(epoch_acc.refcount.native(), 1);
    auto const val_acc = contract.vars.val_execution(val.id)
                             .accumulated_reward_per_token()
                             .load()
                             .native();
    EXPECT_GT(val_acc, 0);
    EXPECT_EQ(val_acc, epoch_acc.value.native());
}

TEST_F(Stake, snapshot_set_same_order_as_consensus_set)
{
    // Add five validators
    auto const auth_address = 0xdeadbeef_address;
    for (uint64_t i = 0; i < 5; ++i) {
        auto const res = add_validator(
            auth_address,
            ACTIVE_VALIDATOR_STAKE,
            0 /* commission */,
            bytes32_t{i + 1} /* unique keys*/);
        EXPECT_FALSE(res.has_error());
    }

    // validators join the consensus set
    skip_to_next_epoch();

    // consensus set copied to snapshot set. they should be the same now
    skip_to_next_epoch();

    // sets should be the same with ids in order.
    EXPECT_EQ(
        contract.vars.valset_consensus.length(),
        contract.vars.valset_snapshot.length());
    for (uint64_t i = 0; i < contract.vars.valset_consensus.length(); ++i) {
        EXPECT_EQ(
            contract.vars.valset_consensus.get(i).load().native(),
            contract.vars.valset_snapshot.get(i).load().native());
    }
}

/////////////////////
// compound / redelegate tests
/////////////////////

TEST_F(Stake, delegate_inter_compound_rewards)
{ // epoch 1 - add validator and 2 delegators
    auto const auth_address = 0xdeadbeef_address;
    auto const reward_decimal_rounding = 999999999999999999;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);

    // add 2 delegators
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        2 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    skip_to_next_epoch();
    // epoch 2 - 3 block reward. this should be split evenly.

    // auth account should get 1/3 of all rewards this epoch
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // auth account should get 2/4 rewards at next epoch
    EXPECT_FALSE(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    // other delegators should get 1/3 of all rewards this epoch
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        4 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    // decimal inaccuracy. off by 1 wei
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        reward_decimal_rounding);

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    skip_to_next_epoch();
    // epoch 3 - 6 block reward. this should be 1/2 validator, 1/4 to each
    // delegator.

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // delegator rewards should be p*(accumulated_reward_per_token(epoch) -
    // accumulated_reward_per_token(del)) + p + r
    // *(accumulated_reward_per_token(curr) -
    // accumulated_reward_per_token(epoch))

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        2 * reward_decimal_rounding + REWARD / 2 + REWARD);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 4);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 4);
}

TEST_F(Stake, delegate_intra_compound_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const reward_decimal_rounding = 999999999999999999;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_EQ(
        ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());

    // add 2 delegators
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        2 * ACTIVE_VALIDATOR_STAKE);
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        3 * ACTIVE_VALIDATOR_STAKE);

    skip_to_next_epoch();

    // auth account should get 1/3 of all rewards this epoch
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // auth account should get 2/4 rewards at next epoch
    EXPECT_FALSE(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    // other delegators should get 1/3 of all rewards this epoch
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        contract.vars.val_execution(val.id).stake().load().native(),
        4 * ACTIVE_VALIDATOR_STAKE);

    // decimal inaccuracy. off by 1 wei
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        reward_decimal_rounding);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        reward_decimal_rounding);

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // auth account should get 3/5 rewards at next epoch
    // other delegators should get 1/5 of all rewards next epoch
    EXPECT_FALSE(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        2 * reward_decimal_rounding + 9 * REWARD / 5);

    EXPECT_EQ(
        contract.vars.delegator(val.id, d0).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 5);
    EXPECT_EQ(
        contract.vars.delegator(val.id, d1).rewards().load().native(),
        2 * reward_decimal_rounding + 3 * REWARD / 5);
}

TEST_F(Stake, delegate_compound_boundary)
{
    // Epoch 1 - Add validator
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    skip_to_next_epoch();

    // Epoch 2 - validator gets reward and compounds it in snapshot
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_FALSE(syscall_snapshot().has_error());

    for (uint32_t i = 0; i < 1; ++i) {
        EXPECT_FALSE(compound(val.id, auth_address).has_error());
        auto del = contract.vars.delegator(val.id, auth_address);
        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.next_delta_stake().load().native(), REWARD);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 4);
    }

    inc_epoch();

    // Epoch 3 - validator compounds touchs state
    pull_delegator_up_to_date(val.id, auth_address);
    {
        auto del = contract.vars.delegator(val.id, auth_address);
        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(del.delta_stake().load().native(), REWARD);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 4);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }

    skip_to_next_epoch();

    // Epoch 4 - Compound rewards should take effect now.
    EXPECT_FALSE(compound(val.id, auth_address).has_error());
    {
        auto del = contract.vars.delegator(val.id, auth_address);

        EXPECT_EQ(del.rewards().load().native(), 0);
        EXPECT_EQ(del.stake().load().native(), ACTIVE_VALIDATOR_STAKE + REWARD);
        EXPECT_EQ(del.delta_stake().load().native(), 0);
        EXPECT_EQ(del.next_delta_stake().load().native(), 0);
        EXPECT_EQ(del.get_delta_epoch().native(), 0);
        EXPECT_EQ(del.get_next_delta_epoch().native(), 0);
    }
}

// compound delegators before and after snapshots
TEST_F(Stake, delegate_compound)
{ // epoch 1
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    auto const reward = 50 * MON;

    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    auto const d2 = 0xbbbbaaaabbbb_address;

    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(delegate(val.id, d2, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_EQ(
        4 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    // epoch 2
    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 1));

    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 1));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());

    EXPECT_FALSE(compound(val.id, d0).has_error());

    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 1));

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 2));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());

    EXPECT_FALSE(compound(val.id, d1).has_error());

    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 1));

    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 3));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());

    EXPECT_FALSE(compound(val.id, d2).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 1));

    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 3));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());

    EXPECT_FALSE(compound(val.id, d0).has_error());

    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 1));

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 3));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());

    EXPECT_FALSE(compound(val.id, d1).has_error());

    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 1));

    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE, ((reward / 4) * 3));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());

    EXPECT_FALSE(compound(val.id, d2).has_error());

    inc_epoch();

    // Epoch 3 - compound reward is now active
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 3), 0);

    check_delegator_c_state(
        val,
        d0,
        ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 1),
        ((reward / 4) * 2));

    check_delegator_c_state(
        val,
        d1,
        ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 2),
        ((reward / 4) * 1));

    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 3), 0);

    EXPECT_FALSE(compound(val.id, d0).has_error());

    EXPECT_FALSE(syscall_snapshot().has_error());

    EXPECT_FALSE(compound(val.id, d1).has_error());

    inc_epoch();
    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, d0);
    pull_delegator_up_to_date(val.id, d1);
    pull_delegator_up_to_date(val.id, d2);

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 6), 0);
    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 6), 0);
    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 5), 0);
    check_delegator_c_state(
        val, d2, ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 6), 0);

    skip_to_next_epoch();

    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE + ((reward / 4) * 6), 0);
}

// compound delegators before and after snapshots then withdraw, val remains
// active
TEST_F(Stake, undelegate_compound)
{
    auto const reward = 10 * MON;
    auto const auth_address = 0xdeadbeef_address;
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    // epoch 2

    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 2));
    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 2));
    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 2));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());
    EXPECT_FALSE(compound(val.id, d0).has_error());
    EXPECT_FALSE(compound(val.id, d1).has_error());

    uint8_t const withdrawal_id{1};

    EXPECT_FALSE(undelegate(val.id, d0, withdrawal_id, ACTIVE_VALIDATOR_STAKE)
                     .has_error());
    check_delegator_c_state(val, d0, 0, 0);

    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());
    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 1));
    check_delegator_c_state(val, d0, 0, 0);

    EXPECT_FALSE(compound(val.id, auth_address).has_error());
    EXPECT_FALSE(compound(val.id, d0).has_error());
    EXPECT_FALSE(compound(val.id, d1).has_error());
    EXPECT_FALSE(undelegate(val.id, d1, withdrawal_id, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    check_delegator_c_state(val, d1, 0, 0);
    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    inc_epoch();
    // Epoch 3
    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + ((reward / 3) * 2),
        (reward / 3));

    check_delegator_c_state(val, d0, ((reward / 3) * 2), 0);
    check_delegator_c_state(val, d1, ((reward / 3) * 2), 0);

    skip_to_next_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(withdraw(val.id, d0, withdrawal_id).has_error());
    EXPECT_FALSE(withdraw(val.id, d1, withdrawal_id).has_error());
    EXPECT_EQ(get_balance(d0), ACTIVE_VALIDATOR_STAKE + ((reward / 3) * 2));
    EXPECT_EQ(get_balance(d1), ACTIVE_VALIDATOR_STAKE + ((reward / 3)));
}

TEST_F(Stake, undelegate_compound_partial)
{
    auto const reward = 10 * MON;
    auto const auth_address = 0xdeadbeef_address;
    auto const d0 = 0xaaaabbbb_address;
    auto const d1 = 0xbbbbaaaa_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_FALSE(delegate(val.id, d0, ACTIVE_VALIDATOR_STAKE).has_error());
    EXPECT_FALSE(delegate(val.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    EXPECT_EQ(
        3 * ACTIVE_VALIDATOR_STAKE,
        contract.vars.val_execution(val.id).stake().load().native());
    skip_to_next_epoch();

    // epoch 2

    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 2));
    check_delegator_c_state(
        val, d0, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 2));
    check_delegator_c_state(
        val, d1, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 2));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());
    EXPECT_FALSE(compound(val.id, d0).has_error());
    EXPECT_FALSE(compound(val.id, d1).has_error());

    uint8_t const withdrawal_id{1};
    EXPECT_FALSE(
        undelegate(val.id, d0, withdrawal_id, ACTIVE_VALIDATOR_STAKE / 2)
            .has_error());
    check_delegator_c_state(val, d0, ACTIVE_VALIDATOR_STAKE / 2, 0);

    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    check_delegator_c_state(
        val, auth_address, ACTIVE_VALIDATOR_STAKE, ((reward / 3) * 1));
    check_delegator_c_state(val, d0, ACTIVE_VALIDATOR_STAKE / 2, (reward / 6));

    EXPECT_FALSE(compound(val.id, auth_address).has_error());
    EXPECT_FALSE(compound(val.id, d0).has_error());
    EXPECT_FALSE(compound(val.id, d1).has_error());
    EXPECT_FALSE(
        undelegate(val.id, d1, withdrawal_id, ACTIVE_VALIDATOR_STAKE / 2)
            .has_error());
    check_delegator_c_state(val, d1, ACTIVE_VALIDATOR_STAKE / 2, 0);
    EXPECT_FALSE(syscall_reward(val.sign_address, reward).has_error());

    inc_epoch();
    // Epoch 3
    check_delegator_c_state(
        val,
        auth_address,
        ACTIVE_VALIDATOR_STAKE + ((reward / 3) * 2),
        (reward / 3));
    check_delegator_c_state(
        val,
        d0,
        ACTIVE_VALIDATOR_STAKE / 2 + ((reward / 3) * 2),
        ((reward / 6)));
    check_delegator_c_state(
        val,
        d1,
        ACTIVE_VALIDATOR_STAKE / 2 + ((reward / 3) * 2),
        ((reward / 6)));

    skip_to_next_epoch();
    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(withdraw(val.id, d0, withdrawal_id).has_error());
    EXPECT_FALSE(withdraw(val.id, d1, withdrawal_id).has_error());
    EXPECT_EQ(get_balance(d0), ACTIVE_VALIDATOR_STAKE / 2 + ((reward / 3)));
    EXPECT_EQ(get_balance(d1), ACTIVE_VALIDATOR_STAKE / 2 + ((reward / 6)));

    check_delegator_c_state(
        val,
        d0,
        ACTIVE_VALIDATOR_STAKE / 2 + ((reward / 3) * 2) + ((reward / 6)),
        ((reward / 6)));
    check_delegator_c_state(
        val,
        d1,
        ACTIVE_VALIDATOR_STAKE / 2 + ((reward / 3) * 2) + ((reward / 3)),
        (reward / 6));
}

/////////////////////
// undelegate tests
/////////////////////

TEST_F(Stake, undelegate_revert_insufficent_funds)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const del_address = 0xaaaabbbb_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_FALSE(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE).has_error());
    skip_to_next_epoch();

    uint8_t const withdrawal_id{1};
    EXPECT_EQ(
        undelegate(
            val.id, del_address, withdrawal_id, 1 + ACTIVE_VALIDATOR_STAKE)
            .assume_error(),
        StakingError::InsufficientStake);

    pull_delegator_up_to_date(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).stake().load().native(),
        ACTIVE_VALIDATOR_STAKE);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        0);

    EXPECT_EQ(get_balance(del_address), 0);
}

TEST_F(Stake, undelegate_boundary_pool)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const del_address = 0xaaaabbbb_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    EXPECT_FALSE(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE).has_error());
    skip_to_next_epoch();

    // undelegate this epoch
    uint8_t const withdrawal_id{1};
    EXPECT_FALSE(
        undelegate(val.id, del_address, withdrawal_id, ACTIVE_VALIDATOR_STAKE)
            .has_error());

    // reward during the block boundary
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // skip delay
    inc_epoch();

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, del_address);

    // validator should get all the rewards since the secondary delegator
    // does not become active in the consensus view until after the window
    // expires.
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 2);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).stake().load().native(),
        0);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).rewards().load().native(),
        0);

    EXPECT_EQ(
        withdraw(val.id, del_address, withdrawal_id).assume_error(),
        StakingError::WithdrawalNotReady);

    // reward the validator in this epoch which the delegator should not
    // get. he has a 1 epoch delay where he continues to deactivate, and
    // another epoch delay for the slashing window in which no rewards are
    // earned.
    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    skip_to_next_epoch();

    // withdrawal should succeed
    EXPECT_FALSE(withdraw(val.id, del_address, withdrawal_id).has_error());

    // primary delegator get all the rewards after the secondary delegator
    // becomes inactive.
    pull_delegator_up_to_date(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD + REWARD / 2);

    // delegator gets his principal and rewards accured during deactivation
    // period.
    EXPECT_EQ(get_balance(del_address), ACTIVE_VALIDATOR_STAKE + REWARD / 2);
}

TEST_F(Stake, undelegate_snapshot_boundary_pool)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const del_address = 0xaaaabbbb_address;
    auto const res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    EXPECT_FALSE(
        delegate(val.id, del_address, ACTIVE_VALIDATOR_STAKE).has_error());
    skip_to_next_epoch();

    // undelegate this epoch
    uint8_t const withdrawal_id{1};

    // reward during the block boundary
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(
        undelegate(val.id, del_address, withdrawal_id, ACTIVE_VALIDATOR_STAKE)
            .has_error());

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    // skip delay
    inc_epoch();

    pull_delegator_up_to_date(val.id, auth_address);
    pull_delegator_up_to_date(val.id, del_address);

    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD / 2);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).stake().load().native(),
        0);
    EXPECT_EQ(
        contract.vars.delegator(val.id, del_address).rewards().load().native(),
        0);

    EXPECT_EQ(
        withdraw(val.id, del_address, withdrawal_id).assume_error(),
        StakingError::WithdrawalNotReady);

    EXPECT_FALSE(syscall_reward(val.sign_address).has_error());

    skip_to_next_epoch();
    skip_to_next_epoch();

    // withdrawal should succeed
    EXPECT_FALSE(withdraw(val.id, del_address, withdrawal_id).has_error());

    pull_delegator_up_to_date(val.id, auth_address);
    EXPECT_EQ(
        contract.vars.delegator(val.id, auth_address).rewards().load().native(),
        REWARD);

    EXPECT_EQ(get_balance(del_address), ACTIVE_VALIDATOR_STAKE + REWARD);
}

/////////////////////
// withdraw tests
/////////////////////

TEST_F(Stake, double_withdraw)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, MIN_VALIDATE_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    skip_to_next_epoch();
    EXPECT_FALSE(
        undelegate(val.id, auth_address, 1, MIN_VALIDATE_STAKE).has_error());
    skip_to_next_epoch();
    skip_to_next_epoch();
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(withdraw(val.id, auth_address, 1).has_error());
    EXPECT_EQ(get_balance(auth_address), MIN_VALIDATE_STAKE);
    EXPECT_EQ(
        withdraw(val.id, auth_address, 1).assume_error(),
        StakingError::UnknownWithdrawalId);
    EXPECT_EQ(get_balance(auth_address), MIN_VALIDATE_STAKE);
}

TEST_F(Stake, withdraw_reusable_id)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const res = add_validator(auth_address, MIN_VALIDATE_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    skip_to_next_epoch();
    EXPECT_FALSE(
        undelegate(val.id, auth_address, 1, MIN_VALIDATE_STAKE).has_error());
    skip_to_next_epoch();
    skip_to_next_epoch();
    EXPECT_FALSE(withdraw(val.id, auth_address, 1).has_error());

    EXPECT_FALSE(
        delegate(val.id, auth_address, ACTIVE_VALIDATOR_STAKE).has_error());

    skip_to_next_epoch();
    skip_to_next_epoch();

    EXPECT_FALSE(
        undelegate(val.id, auth_address, 1, MIN_VALIDATE_STAKE).has_error());

    skip_to_next_epoch();
    skip_to_next_epoch();
    EXPECT_FALSE(withdraw(val.id, auth_address, 1).has_error());
}

/////////////////////
// claim_rewards tests
/////////////////////

TEST_F(Stake, claim_rewards)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(val.has_error());
    skip_to_next_epoch();
    EXPECT_FALSE(syscall_reward(val.value().sign_address).has_error());
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(claim_rewards(val.value().id, auth_address).has_error());
    EXPECT_EQ(get_balance(auth_address), REWARD);
}

TEST_F(Stake, claim_noop)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(val.has_error());
    skip_to_next_epoch();
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(claim_rewards(val.value().id, auth_address).has_error());
    EXPECT_EQ(get_balance(auth_address), 0);
}

TEST_F(Stake, claim_rewards_compound)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(val.has_error());
    skip_to_next_epoch();

    EXPECT_FALSE(syscall_reward(val.value().sign_address).has_error());
    EXPECT_EQ(get_balance(auth_address), 0);
    EXPECT_FALSE(claim_rewards(val.value().id, auth_address).has_error());
    EXPECT_EQ(get_balance(auth_address), REWARD);

    EXPECT_FALSE(compound(val.value().id, auth_address).has_error());
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_reward(val.value().sign_address).has_error());

    EXPECT_EQ(get_balance(auth_address), REWARD);
    EXPECT_FALSE(claim_rewards(val.value().id, auth_address).has_error());
    EXPECT_EQ(get_balance(auth_address), 2 * REWARD);

    EXPECT_FALSE(compound(val.value().id, auth_address).has_error());

    check_delegator_c_state(
        val.value(), auth_address, ACTIVE_VALIDATOR_STAKE, 0);
    inc_epoch();
    check_delegator_c_state(
        val.value(), auth_address, ACTIVE_VALIDATOR_STAKE, 0);
}

///////////////////////
// sys_call_reward tests
////////////////////////

TEST_F(Stake, reward_unknown_validator)
{
    auto const unknown = Address{0xabcdef};
    EXPECT_EQ(
        syscall_reward(unknown).assume_error(),
        StakingError::NotInValidatorSet);
}

TEST_F(Stake, reward_crash_no_snapshot_missing_validator)
{
    auto const auth_address = 0xdeadbeef_address;
    auto const val = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(val.has_error());
    inc_epoch();
    EXPECT_EQ(
        syscall_reward(val.value().sign_address).assume_error(),
        StakingError::NotInValidatorSet);
}

////////////////////////
// sys_call_snapshot tests
////////////////////////

TEST_F(Stake, multiple_snapshot_error)
{
    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_TRUE(syscall_snapshot().has_error());
    inc_epoch();
    EXPECT_FALSE(syscall_snapshot().has_error());
}

TEST_F(Stake, valset_exceeds_n)
{
    auto const auth_address = 0xdeadbeef_address;
    static_assert(ACTIVE_VALSET_SIZE < 1000);

    std::vector<std::pair<u64_be, uint256_t>> vals;
    for (uint32_t i = 1; i <= 1000u; ++i) {
        uint256_t const stake = ACTIVE_VALIDATOR_STAKE + 1000 - i;
        auto const val = add_validator(auth_address, stake, 0, bytes32_t{i});
        ASSERT_FALSE(val.has_error());
        vals.emplace_back(val.value().id, stake);
    }
    EXPECT_EQ(contract.vars.valset_execution.length(), 1000u);

    // create the consensus valset
    skip_to_next_epoch();
    EXPECT_EQ(contract.vars.valset_snapshot.length(), 0);
    EXPECT_EQ(contract.vars.valset_consensus.length(), ACTIVE_VALSET_SIZE);

    auto is_in_valset = [&](u64_be const &val_id) -> bool {
        auto const valset = contract.vars.valset_consensus;
        for (uint64_t i = 0; i < valset.length(); ++i) {
            if (valset.get(i).load() == val_id) {
                return true;
            }
        }
        return false;
    };
    for (uint32_t i = 1; i <= 1000; ++i) {
        auto const &[val_id, stake] = vals[i - 1];
        if (i <= ACTIVE_VALSET_SIZE) {
            EXPECT_TRUE(is_in_valset(val_id));
            EXPECT_EQ(
                contract.vars.consensus_view(val_id).stake().load().native(),
                stake);
        }
        else {
            EXPECT_FALSE(is_in_valset(val_id));
            EXPECT_EQ(
                contract.vars.consensus_view(val_id).stake().load().native(),
                0);
        }
    }

    skip_to_next_epoch();

    // now both valsets should be active valset size
    EXPECT_EQ(contract.vars.valset_snapshot.length(), ACTIVE_VALSET_SIZE);
    EXPECT_EQ(contract.vars.valset_consensus.length(), ACTIVE_VALSET_SIZE);
}

////////////////////////
// sys_call_epoch_change tests
////////////////////////

TEST_F(Stake, epoch_goes_backwards)
{
    EXPECT_FALSE(syscall_on_epoch_change(3).has_error());
    EXPECT_TRUE(syscall_on_epoch_change(1).has_error());
    EXPECT_TRUE(syscall_on_epoch_change(2).has_error());
    EXPECT_TRUE(syscall_on_epoch_change(3).has_error());
    EXPECT_FALSE(syscall_on_epoch_change(4).has_error());
}

TEST_F(Stake, contract_bootstrap)
{
    // This test simulates the bootstrap flow for a live chain.
    //
    // First, some definitions.
    //   Forkpoint `N`: Staking precompiles are made accessible.
    //   Forkpoint `M`: Consensus starts issuing rewards. Note that M > N.
    //   Epoch `E`: The epoch of forkpoint m.
    //
    // At N, the first transaction will be an epoch change from 0 to E-1. This
    // ensures the execution view of the epoch is in accordance with the
    // consensus view of the epoch. Validators will add themselves to the
    // execution valset during E-1 and no rewards will be issued. At forkpoint
    // M, staking begins.

    constexpr uint64_t E = 20;
    contract.vars.epoch.store(0);

    // consensus initializes the epoch by calling epoch change
    EXPECT_FALSE(syscall_on_epoch_change(E - 1).has_error());

    // sets should be empty
    EXPECT_EQ(contract.vars.valset_execution.length(), 0);
    EXPECT_EQ(contract.vars.valset_snapshot.length(), 0);
    EXPECT_EQ(contract.vars.valset_consensus.length(), 0);
    EXPECT_EQ(contract.vars.epoch.load().native(), E - 1);

    auto const auth_address = 0xdeadbeef_address;

    // Add two validators
    auto res =
        add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1000});
    ASSERT_FALSE(res.has_error());
    auto const val1 = res.assume_value();
    res = add_validator(auth_address, MIN_VALIDATE_STAKE, 0, bytes32_t{0x1002});
    ASSERT_FALSE(res.has_error());
    auto const val2 = res.assume_value();

    // delegate with validator 1
    auto const d1 = 0xaaaabbbb_address;
    EXPECT_FALSE(delegate(val1.id, d1, 10 * MON).has_error());
    EXPECT_FALSE(delegate(val1.id, d1, ACTIVE_VALIDATOR_STAKE).has_error());

    // verify no undelegations before activation
    EXPECT_TRUE(undelegate(val1.id, d1, 1, ACTIVE_VALIDATOR_STAKE).has_error());

    // verify withdrawals don't work
    for (uint16_t i = 0; i <= std::numeric_limits<uint8_t>::max(); ++i) {
        EXPECT_EQ(
            withdraw(val1.id, d1, static_cast<uint8_t>(i)).assume_error(),
            StakingError::UnknownWithdrawalId);
    }

    EXPECT_FALSE(syscall_snapshot().has_error());
    EXPECT_FALSE(syscall_on_epoch_change(E).has_error());

    // All delegators have their principal (no rewards earned)
    check_delegator_c_state(val1, auth_address, MIN_VALIDATE_STAKE, 0);
    check_delegator_c_state(val1, d1, 10 * MON + ACTIVE_VALIDATOR_STAKE, 0);
    check_delegator_c_state(val2, auth_address, MIN_VALIDATE_STAKE, 0);

    // only one of the validators had enough stake to be active.
    EXPECT_EQ(contract.vars.valset_consensus.length(), 1);
    EXPECT_EQ(contract.vars.valset_snapshot.length(), 0);
    EXPECT_EQ(
        contract.vars.valset_consensus.get(0).load().native(),
        val1.id.native());

    // check: accumulator refcounts are cleared
    auto const acc =
        contract.vars.accumulated_reward_per_token(E - 1, val1.id).load();
    EXPECT_EQ(acc.refcount.native(), 0);
    EXPECT_EQ(acc.value.native(), 0);
    auto const acc2 =
        contract.vars.accumulated_reward_per_token(E - 1, val2.id).load();
    EXPECT_EQ(acc2.refcount.native(), 0);
    EXPECT_EQ(acc2.value.native(), 0);
}

TEST_F(Stake, zero_reward_epochs)
{
    auto const auth_address = 0xdeadbeef_address;
    std::array<Address, 4> delegators{
        0xdead_address, 0xbeef_address, 0x600d_address, 0xbadd_address};
    std::vector<ValResult> validators;
    uint256_t const DELEGATOR_STAKE = 1000000 * MON;

    contract.vars.epoch.store(49); // start at epoch 49

    for (uint64_t i = 0; i < 10; ++i) {
        // add validator
        uint256_t const commission = (i % 2 == 0) ? MON * 10 / 100 : 0;
        auto const res = add_validator(
            auth_address, ACTIVE_VALIDATOR_STAKE, commission, bytes32_t{i + 1});
        ASSERT_FALSE(res.has_error());
        validators.push_back(res.value());

        // add some delegators to each validator
        for (auto const &d : delegators) {
            EXPECT_FALSE(
                delegate(res.value().id, d, DELEGATOR_STAKE).has_error());
        }
    }

    skip_to_next_epoch(); // epoch 50
    for (uint64_t epoch = 51; epoch <= 60; ++epoch) {
        for (uint64_t block = 0; block < 50; ++block) {
            auto const proposer =
                validators[block % validators.size()].sign_address;
            if (block == 40) {
                EXPECT_FALSE(syscall_snapshot().has_error());
            }
            EXPECT_FALSE(syscall_reward(proposer, 0).has_error());
        }
        EXPECT_FALSE(syscall_on_epoch_change(epoch).has_error());
    }

    // check no staking emissions occurred
    EXPECT_EQ(
        get_balance(STAKING_CA),
        ACTIVE_VALIDATOR_STAKE * validators.size() +
            DELEGATOR_STAKE * delegators.size() * validators.size());
    for (auto const &v : validators) {
        auto val_info = contract.vars.val_execution(v.id);
        EXPECT_EQ(
            val_info.stake().load().native(),
            ACTIVE_VALIDATOR_STAKE + DELEGATOR_STAKE * delegators.size());
        EXPECT_EQ(val_info.accumulated_reward_per_token().load().native(), 0);
        EXPECT_EQ(val_info.unclaimed_rewards().load().native(), 0);

        pull_delegator_up_to_date(v.id, auth_address);
        auto auth_del = contract.vars.delegator(v.id, auth_address);
        EXPECT_EQ(auth_del.stake().load().native(), ACTIVE_VALIDATOR_STAKE);
        EXPECT_EQ(auth_del.accumulated_reward_per_token().load().native(), 0);
        EXPECT_EQ(auth_del.rewards().load().native(), 0);

        for (auto const &d : delegators) {
            pull_delegator_up_to_date(v.id, d);
            auto del_info = contract.vars.delegator(v.id, d);
            EXPECT_EQ(del_info.stake().load().native(), DELEGATOR_STAKE);
            EXPECT_EQ(
                del_info.accumulated_reward_per_token().load().native(), 0);
            EXPECT_EQ(del_info.rewards().load().native(), 0);
        }
    }
}

//////////////////
// Getter Tests //
//////////////////

TEST_F(Stake, get_valset_empty)
{
    EXPECT_FALSE(get_valset(0).has_error());
    EXPECT_FALSE(get_valset(std::numeric_limits<uint32_t>::max()).has_error());
}

TEST_F(Stake, empty_get_delegators_for_validator_getter)
{
    {
        // validator doesn't exist
        auto const [done, _, delegators] =
            contract.get_delegators_for_validator(
                u64_be{1}, Address{}, std::numeric_limits<uint32_t>::max());
        EXPECT_TRUE(done);
        EXPECT_TRUE(delegators.empty());
    }

    {
        // validator exists, bogus delegator start pointer provided
        auto const res =
            add_validator(0xdeadbeef_address, ACTIVE_VALIDATOR_STAKE);
        ASSERT_FALSE(res.has_error());
        auto const [done, _, delegators] =
            contract.get_delegators_for_validator(
                res.value().id,
                0x1337_address,
                std::numeric_limits<uint32_t>::max());
        EXPECT_TRUE(done);
        EXPECT_TRUE(delegators.empty());
    }
}

TEST_F(Stake, empty_get_validators_for_delegator_getter)
{
    {
        // validator doesn't exist
        auto const [done, _, validators] =
            contract.get_validators_for_delegator(
                Address{0x1337},
                u64_be{},
                std::numeric_limits<uint32_t>::max());
        EXPECT_TRUE(done);
        EXPECT_TRUE(validators.empty());
    }

    {
        // validator exists, bogus val_id start pointer provided
        auto const res =
            add_validator(0xdeadbeef_address, ACTIVE_VALIDATOR_STAKE);
        ASSERT_FALSE(res.has_error());
        auto const [done, _, delegators] =
            contract.get_validators_for_delegator(
                0xdeadbeef_address,
                u64_be{200},
                std::numeric_limits<uint32_t>::max());
        EXPECT_TRUE(done);
        EXPECT_TRUE(delegators.empty());
    }
}

TEST_F(Stake, get_delegators_for_validator)
{
    auto const auth_address = 0xdeadbeef_address;
    auto res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    std::set<Address> delegators;
    delegators.emplace(auth_address);
    for (uint32_t i = 0; i < 999; ++i) {
        // delegate twice to make sure dups are handled correctly
        auto const del = Address{i + 1};
        ASSERT_FALSE(delegate(val.id, del, 100_u256 * MON).has_error());
        ASSERT_FALSE(delegate(val.id, del, 100_u256 * MON).has_error());
        delegators.emplace(del);
    }

    {
        auto const [done, _, contract_delegators] =
            contract.get_delegators_for_validator(
                val.id, Address{}, std::numeric_limits<uint32_t>::max());
        EXPECT_TRUE(done);
        EXPECT_EQ(delegators.size(), contract_delegators.size());
        for (auto const &del : contract_delegators) {
            EXPECT_TRUE(delegators.contains(del));
        }
    }

    // activate the stake so it can be undelegated
    skip_to_next_epoch();

    // undelegate a couple
    ASSERT_FALSE(
        undelegate(val.id, Address{20}, 1, 200_u256 * MON).has_error());
    delegators.erase(Address{20});
    ASSERT_FALSE(
        undelegate(val.id, Address{101}, 1, 200_u256 * MON).has_error());
    delegators.erase(Address{101});
    ASSERT_FALSE(
        undelegate(val.id, Address{500}, 1, 200_u256 * MON).has_error());
    delegators.erase(Address{500});

    {
        auto const [done, _, contract_delegators] =
            contract.get_delegators_for_validator(
                val.id, Address{}, std::numeric_limits<uint32_t>::max());
        EXPECT_TRUE(done);
        EXPECT_EQ(delegators.size(), contract_delegators.size());
        for (auto const &del : contract_delegators) {
            EXPECT_TRUE(delegators.contains(del));
        }
    }
}

TEST_F(Stake, get_validators_for_delegator)
{
    auto const auth_address = 0xdeadbeef_address;
    std::unordered_set<uint64_t> validators;
    for (uint32_t i = 0; i < 999; ++i) {
        auto res = add_validator(
            auth_address,
            ACTIVE_VALIDATOR_STAKE,
            0 /* commission */,
            bytes32_t{i + 1000} /* secret */);
        ASSERT_FALSE(res.has_error());
        validators.emplace(res.value().id.native());
    }

    auto const del = 0x1337_address;
    for (auto const val_id : validators) {
        // delegate twice with every validator
        ASSERT_FALSE(delegate(u64_be{val_id}, del, 100_u256 * MON).has_error());
        ASSERT_FALSE(delegate(u64_be{val_id}, del, 100_u256 * MON).has_error());
    }

    {
        auto const [done, _, contract_validators] =
            contract.get_validators_for_delegator(
                del, u64_be{}, std::numeric_limits<uint32_t>::max());
        EXPECT_EQ(validators.size(), contract_validators.size());
        for (u64_be const val_id : contract_validators) {
            EXPECT_TRUE(validators.contains(val_id.native()));
        }
    }

    // activate the stake so it can be undelegated
    skip_to_next_epoch();

    // undelegate a couple
    ASSERT_FALSE(undelegate(u64_be{20}, del, 1, 200_u256 * MON).has_error());
    validators.erase(20);
    ASSERT_FALSE(undelegate(u64_be{101}, del, 1, 200_u256 * MON).has_error());
    validators.erase(101);
    ASSERT_FALSE(undelegate(u64_be{500}, del, 1, 200_u256 * MON).has_error());
    validators.erase(500);

    {
        auto const [done, _, contract_validators] =
            contract.get_validators_for_delegator(
                del, u64_be{}, std::numeric_limits<uint32_t>::max());
        EXPECT_TRUE(done);
        EXPECT_EQ(validators.size(), contract_validators.size());
        for (u64_be const val_id : contract_validators) {
            EXPECT_TRUE(validators.contains(val_id.native()));
        }
    }
}

TEST_F(Stake, get_valset_paginated_reads)
{
    auto const auth_address = 0xdeadbeef_address;
    for (uint32_t i = 0; i < 999; ++i) {
        auto res = add_validator(
            auth_address, ACTIVE_VALIDATOR_STAKE, 0, bytes32_t{i + 1});
        ASSERT_FALSE(res.has_error());
    }

    // read valset in one read
    auto const [done1, _, valset_one_read] = contract.get_valset(
        contract.vars.valset_execution,
        0,
        std::numeric_limits<uint32_t>::max());
    EXPECT_TRUE(done1);
    EXPECT_EQ(valset_one_read.size(), 999);

    // read valset in pages
    bool done2 = false;
    u32_be next_index = 0;
    std::vector<u64_be> valset_paginated;
    do {
        auto paginated_res = contract.get_valset(
            contract.vars.valset_execution,
            next_index.native(),
            PAGINATED_RESULTS_SIZE);
        std::vector<u64_be> valset_page;
        std::tie(done2, next_index, valset_page) = std::move(paginated_res);
        valset_paginated.insert_range(valset_paginated.end(), valset_page);
    }
    while (!done2);

    EXPECT_EQ(valset_paginated.size(), valset_one_read.size());
    EXPECT_TRUE(valset_paginated == valset_one_read);
}

TEST_F(Stake, get_delegators_for_validator_paginated_reads)
{
    auto const auth_address = 0xdeadbeef_address;
    auto res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();

    for (uint32_t i = 0; i < 999; ++i) {
        // delegate twice to make sure dups are handled correctly
        auto const del = Address{i + 1};
        ASSERT_FALSE(delegate(val.id, del, 100_u256 * MON).has_error());
        ASSERT_FALSE(delegate(val.id, del, 100_u256 * MON).has_error());
    }

    // read all the delegators
    auto const [done1, _, delegators_one_read] =
        contract.get_delegators_for_validator(
            val.id, Address{}, std::numeric_limits<uint32_t>::max());
    EXPECT_TRUE(done1);
    EXPECT_EQ(
        delegators_one_read.size(),
        1000); // note: this is 1000 because the auth address is a delegator

    // read all delegators using paginated reads
    bool done2 = false;
    Address next_delegator{};
    std::vector<Address> delegators_paginated;
    do {
        auto paginated_res = contract.get_delegators_for_validator(
            val.id, next_delegator, PAGINATED_RESULTS_SIZE);
        std::vector<Address> delegators_page;
        std::tie(done2, next_delegator, delegators_page) =
            std::move(paginated_res);
        delegators_paginated.insert_range(
            delegators_paginated.end(), delegators_page);
    }
    while (!done2);

    // The two vectors should be equal.  This ensures that RPC style reads match
    // what we expect using internal calls.
    EXPECT_EQ(delegators_paginated.size(), delegators_one_read.size());
    EXPECT_TRUE(delegators_paginated == delegators_one_read);
}

////////////////////
// Solvency Tests //
////////////////////

TEST_F(Stake, validator_insolvent)
{
    auto const auth_address = 0xdeadbeef_address;
    auto res = add_validator(auth_address, MIN_VALIDATE_STAKE);
    auto const val = res.assume_value();

    skip_to_next_epoch();

    // simulate an accumulator error
    contract.vars.val_execution(val.id).accumulated_reward_per_token().store(
        10_u256 * MON);

    EXPECT_EQ(
        claim_rewards(val.id, auth_address).assume_error(),
        StakingError::SolvencyError);
}

TEST_F(Stake, withdrawal_insolvent)
{
    auto const auth_address = 0xdeadbeef_address;
    auto res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    auto const val = res.assume_value();

    skip_to_next_epoch(); // activate the stake
    EXPECT_FALSE(undelegate(val.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    // simulate an accumulator error before the epoch change.  this is so the
    // error becomes part of the pending undelegation during this epoch.
    contract.vars.val_execution(val.id).accumulated_reward_per_token().store(
        10_u256 * MON);

    skip_to_next_epoch(); // withdrawal is insolvent, but inactive
    skip_to_next_epoch(); // withdrawal is insolvent and active.

    EXPECT_EQ(
        withdraw(val.id, auth_address, 1).assume_error(),
        StakingError::SolvencyError);
}

TEST_F(Stake, withdrawal_state_override)
{
    auto const auth_address = 0xdeadbeef_address;
    auto res = add_validator(auth_address, ACTIVE_VALIDATOR_STAKE);
    auto const val = res.assume_value();

    skip_to_next_epoch(); // activate the stake
    EXPECT_FALSE(undelegate(val.id, auth_address, 1, ACTIVE_VALIDATOR_STAKE)
                     .has_error());

    skip_to_next_epoch(); // withdrawal inactive
    skip_to_next_epoch(); // withdrawal active.

    // make the contract insolvent. this could be achieved by an eth call state
    // override.
    state.subtract_from_balance(
        STAKING_CA, intx::be::load<uint256_t>(state.get_balance(STAKING_CA)));

    EXPECT_THROW((void)withdraw(val.id, auth_address, 1), MonadException);
}

////////////////
// Dust Tests //
////////////////

TEST_F(Stake, dust_hunter)
{
    // This test binary searches the space between [0, 10e18] and finds the
    // largest value that produces 0 rewards.
    //
    // To keep each iteration hermetic, a new validator pool is created. A
    // delegator join with a stake somewhere in the search space. The pool is
    // rewarded, and success condition is the delegator receieves nonzero
    // rewards. The tests asserts that our dust threshold is higher than the
    // minimum value that produces dust in the contract.

    uint256_t lo = 0;
    uint256_t hi = 10 * MON;
    uint64_t keydata = 1;
    auto const auth_address = 0xdeadbeef_address;
    auto const delegator = 0x1234_address;

    auto const rewards_fn = [this, &auth_address, &delegator](
                                uint256_t const &stake,
                                uint64_t &keydata) -> uint256_t {
        auto const res = add_validator(
            auth_address, ACTIVE_VALIDATOR_STAKE, 0, bytes32_t{keydata});
        EXPECT_FALSE(res.has_error());

        ++keydata; // validator keys cannot be reused
        auto const val = res.assume_value();

        // set the delegator's stake manually instead of going through
        // delegation precompile to bypass the dust threshold.
        contract.vars.delegator(val.id, delegator).stake().store(stake);
        skip_to_next_epoch();
        EXPECT_FALSE(syscall_reward(val.sign_address).has_error());
        pull_delegator_up_to_date(val.id, delegator);
        return contract.vars.delegator(val.id, delegator)
            .rewards()
            .load()
            .native();
    };
    while (lo < hi) {
        uint256_t const mid = lo + ((hi - lo + 1) / 2);
        uint256_t const rewards = rewards_fn(mid, keydata);
        if (rewards == 0) {
            lo = mid;
        }
        else {
            hi = mid - 1;
        }
    }

    uint256_t const needle = lo;
    EXPECT_EQ(rewards_fn(needle, keydata), 0);
    EXPECT_GT(rewards_fn(needle + 1, keydata), 0);
    EXPECT_GE(DUST_THRESHOLD, needle);
}

TEST_F(Stake, delegate_dust)
{
    auto const delegator = 0xaaaa_address;
    auto const res = add_validator(0xdeadbeef_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    skip_to_next_epoch();

    // delegate
    EXPECT_EQ(
        delegate(val.id, delegator, DUST_THRESHOLD / 2).assume_error(),
        StakingError::DelegationTooSmall);
    EXPECT_EQ(
        delegate(val.id, delegator, DUST_THRESHOLD - 1).assume_error(),
        StakingError::DelegationTooSmall);

    // above the threshold
    EXPECT_FALSE(delegate(val.id, delegator, DUST_THRESHOLD).has_error());

    // compound (invokes delegate)
    contract.vars.delegator(val.id, delegator)
        .rewards()
        .store(DUST_THRESHOLD / 2);
    EXPECT_EQ(
        compound(val.id, delegator).assume_error(),
        StakingError::DelegationTooSmall);
    contract.vars.delegator(val.id, delegator)
        .rewards()
        .store(DUST_THRESHOLD - 1);
    EXPECT_EQ(
        compound(val.id, delegator).assume_error(),
        StakingError::DelegationTooSmall);

    // above the threshold
    contract.vars.delegator(val.id, delegator).rewards().store(DUST_THRESHOLD);
    EXPECT_FALSE(compound(val.id, delegator).has_error());
}

TEST_F(Stake, undelegate_dust)
{
    auto const delegator = 0xaaaa_address;
    auto const res = add_validator(0xdeadbeef_address, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    skip_to_next_epoch();

    // delegate over the dust threshold, with an extra 300 wei dust.
    EXPECT_FALSE(delegate(val.id, delegator, DUST_THRESHOLD + 300).has_error());

    // activate delegation
    skip_to_next_epoch();
    pull_delegator_up_to_date(val.id, delegator);
    EXPECT_EQ(
        contract.vars.delegator(val.id, delegator).stake().load().native(),
        DUST_THRESHOLD + 300);

    // undelegate, leaving the 300 wei in the delegator
    EXPECT_FALSE(
        undelegate(val.id, delegator, 1 /* withdrawal id */, DUST_THRESHOLD)
            .has_error());

    // withdrawal request should include the dust
    auto const withdrawal_request =
        contract.vars.withdrawal_request(val.id, delegator, 1).load_checked();
    ASSERT_TRUE(withdrawal_request.has_value());
    EXPECT_EQ(withdrawal_request->amount.native(), DUST_THRESHOLD + 300);

    // delegator should have zero balance
    pull_delegator_up_to_date(val.id, delegator);
    EXPECT_EQ(
        contract.vars.delegator(val.id, delegator).stake().load().native(), 0);

    skip_to_next_epoch(); // undelegation processed
    skip_to_next_epoch(); // withdrawal available
    EXPECT_FALSE(
        withdraw(val.id, delegator, 1 /* withdrawal id */).has_error());
    EXPECT_EQ(get_balance(delegator), DUST_THRESHOLD + 300);
}

//////////////////
// Events Tests //
//////////////////

TEST_F(Stake, events)
{
    auto const auth = 0xdeadbeef_address;

    // Add validator with enough stake to activate immediately
    //   1. Validator created
    //   2. Validator status changed to active.
    //   3. Delegate event
    auto const res = add_validator(auth, ACTIVE_VALIDATOR_STAKE);
    ASSERT_FALSE(res.has_error());
    auto const val = res.value();
    size_t seen_events = 0;
    EXPECT_EQ(state.logs().size(), 3);
    seen_events += 3;

    // Change to new commission
    //  1. Commission changed event
    ASSERT_FALSE(change_commission(val.id, auth, MON * 25 / 100).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    seen_events += 1;

    // Change to the same commission. No events emitted
    ASSERT_FALSE(change_commission(val.id, auth, MON * 25 / 100).has_error());
    EXPECT_EQ(state.logs().size(), seen_events);

    // Epoch change
    //  1. Epoch changed event
    skip_to_next_epoch();
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    seen_events += 1;

    // Undelegate, setting validator inactive
    //   1. Undelegate event
    //   2. Validator status changed to inactive
    ASSERT_FALSE(undelegate(val.id, auth, 1, 50 * MON).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 2);
    seen_events += 2;

    // Undelegate without changing validator state
    //   1. Undelegate event
    ASSERT_FALSE(undelegate(val.id, auth, 2, 10 * MON).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    seen_events += 1;

    // Delegate without changing validator state
    //  1. Delegate event
    ASSERT_FALSE(delegate(val.id, auth, 10 * MON).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    seen_events += 1;

    // Delegate, setting validator active
    //  1. Delegate event
    //  2. Validator status changed
    ASSERT_FALSE(delegate(val.id, auth, 50 * MON).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 2);
    seen_events += 2;

    // Claim with no rewards. No events emitted
    ASSERT_FALSE(claim_rewards(val.id, auth).has_error());
    EXPECT_EQ(state.logs().size(), seen_events);

    // Reward syscall
    //  1. Reward originating from the contract
    ASSERT_FALSE(syscall_reward(val.sign_address).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    EXPECT_EQ(state.logs().back().topics[2], abi_encode_address(SYSTEM_SENDER));
    seen_events += 1;

    // Claim with nonzero rewards.
    //   1. Claim event
    ASSERT_FALSE(claim_rewards(val.id, auth).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    seen_events += 1;

    // External reward
    //  1. Reward originating from the sender
    ASSERT_FALSE(external_reward(val.id, auth, 5 * MON).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    EXPECT_EQ(state.logs().back().topics[2], abi_encode_address(auth));
    seen_events += 1;

    // Compound without changing validator state
    //  1. Claim event
    //  2. Delegate event
    ASSERT_FALSE(compound(val.id, auth).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 2);
    seen_events += 2;

    // Compound with no rewards.  Note that all reward for `auth` were just
    // compounded in the last step. No events emitted.
    ASSERT_FALSE(compound(val.id, auth).has_error());
    EXPECT_EQ(state.logs().size(), seen_events);

    // Withdraw one of the pending delegations
    //   1. Withdraw event
    skip_to_next_epoch();
    skip_to_next_epoch();
    seen_events += 2; // two epoch changed events
    ASSERT_FALSE(withdraw(val.id, auth, 1).has_error());
    EXPECT_EQ(state.logs().size(), seen_events + 1);
    seen_events += 1;

    // All logs should come from the staking contract
    for (auto const &log : state.logs()) {
        EXPECT_EQ(log.address, STAKING_CA);
    }

    // compute data hash and topics hash
    byte_string data_blob;
    byte_string topics_blob;
    for (auto const &log : state.logs()) {
        topics_blob += abi_encode_uint<u64_be>(log.topics.size());
        for (bytes32_t const &topic : log.topics) {
            topics_blob += byte_string{topic};
        }
        data_blob += abi_encode_uint<u64_be>(log.data.size());
        data_blob += log.data;
    }
    auto const data_hash = to_bytes(blake3(data_blob));
    auto const topics_hash = to_bytes(blake3(topics_blob));

    // If intentionally bumping the hashes, this script tidies the gtest output:
    // awk '{gsub(/[- ]/, ""); print}'
    EXPECT_EQ(
        data_hash,
        0x963BADF92D0C30030E575232A2FDF1333D60D7DE3B6FB275E61451C108F0E2D3_bytes32)
        << "Staking event change requires a hardfork!";
    EXPECT_EQ(
        topics_hash,
        0x698CB2EE95A576037A3D5EDDA5FFA5ABC8741E6DB69883C899CC93C0EBB55AB6_bytes32)
        << "Staking event change requires a hardfork!";
}
