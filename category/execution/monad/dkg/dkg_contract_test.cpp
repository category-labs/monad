// Copyright (C) 2026 Category Labs, Inc.

#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/dkg/dkg_contract.hpp>
#include <category/execution/monad/dkg/dkg_error.hpp>
#include <category/execution/monad/dkg/execute_block_prelude.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <cstring>
#include <memory>

using namespace monad;
using namespace monad::dkg;
using namespace monad::literals;

namespace
{

    uint64_t abi_word_u64(byte_string_view const encoded, size_t const word)
    {
        return load_be_unsafe<uint64_t>(encoded.data() + word * 32 + 24);
    }

    byte_string registration_call()
    {
        return from_hex("0x00000000000000000000000000000000000000"
                        "00000000000000000000000002"
                        "0000000000000000000000007e5f4552091a6912"
                        "5d5dfcb7b8c2659029395bdf"
                        "0000000000000000000000000000000000000000"
                        "000000000000000000000003"
                        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                        "aaaaaaaaaaaaaaaaaaaaaaaa"
                        "0000000000000000000000000000000000000000"
                        "000000000000000000000004"
                        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                        "bbbbbbbbbbbbbbbbbbbbbbbb"
                        "cccccccccccccccccccccccccccccccccccccccc"
                        "cccccccccccccccccccccccc")
            .value();
    }

    byte_string registration_call(uint64_t const epoch)
    {
        byte_string result = registration_call();
        bytes32_t const encoded_epoch = abi_encode_uint(u64_be{epoch});
        std::memcpy(result.data(), encoded_epoch.bytes, sizeof(encoded_epoch));
        return result;
    }

    byte_string pc_qc_call(uint64_t const epoch, uint32_t const dealer = 0)
    {
        byte_string result;
        result += abi_encode_uint(u64_be{epoch});
        result += abi_encode_uint(u64_be{64});
        result += abi_encode_uint(u32_be{dealer});
        result +=
            0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd_bytes32;
        result += abi_encode_uint(u64_be{96});
        result += abi_encode_uint(u64_be{1});
        result += abi_encode_uint(u32_be{0});
        result +=
            0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_bytes32;
        result +=
            0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_bytes32;
        return result;
    }

    byte_string bve_qc_call(uint64_t const epoch, uint32_t const dealer = 0)
    {
        byte_string result;
        result += abi_encode_uint(u64_be{epoch});
        result += abi_encode_uint(u64_be{64});
        result += abi_encode_uint(u32_be{dealer});
        result +=
            0xdddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd_bytes32;
        result +=
            0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc_bytes32;
        result += abi_encode_uint(u64_be{128});
        result += abi_encode_uint(u64_be{1});
        result += abi_encode_uint(u32_be{0});
        result +=
            0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_bytes32;
        result +=
            0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff_bytes32;
        return result;
    }

    byte_string result_call()
    {
        byte_string result;
        result += abi_encode_uint(u64_be{2});
        result += abi_encode_uint(u64_be{64});
        result +=
            0x1111111111111111111111111111111111111111111111111111111111111111_bytes32;
        for (uint64_t i = 1; i <= 18; ++i) {
            result += abi_encode_uint(u64_be{i});
        }
        result += abi_encode_uint(u64_be{20 * 32});
        result += abi_encode_uint(u64_be{1});
        result += abi_encode_uint(u32_be{0});
        // Rust `sign_dkg_done_qc` vector for signing key 1. It signs the
        // already-SHA-256-hashed protocol transcript (no Ethereum prefix and
        // no second hash).
        result +=
            0x45992c99e5aaa4089a9afdbc3fbc00494a067ab0a73e89ab39684bb56a0a37a8_bytes32;
        result +=
            0x70fd863a84efab09ecc59bd0c6000a8a80a39903f77286d08169671088e9ae7f_bytes32;
        return result;
    }

    struct NativeDkgContractTest : ::testing::Test
    {
        vm::VM vm;
        mpt::Db db{std::make_unique<OnDiskMachine>()};
        TrieDb trie_db{db};
        BlockState block_state{trie_db, vm};
        State state{block_state, Incarnation{0, 0}};
        NoopCallTracer call_tracer;
        DkgContract contract{state, call_tracer};

        static constexpr Address validator =
            0x1111111111111111111111111111111111111111_address;

        void SetUp() override
        {
            state.add_to_balance(staking::STAKING_CA, 0);
            staking::StakingContract::Variables staking{state};
            staking.epoch.store(u64_be{1});
            execute_block_prelude<MonadTraits<MONAD_NEXT>>(state);
            ASSERT_TRUE(state.account_exists(DKG_CA));
            ASSERT_EQ(state.get_nonce(DKG_CA), 1);
            staking.val_id(validator).store(u64_be{1});
            staking.valset_consensus.push(u64_be{1});
            staking.consensus_view(u64_be{1}).stake().store(
                u256_be{staking::limits::active_validator_stake<
                    MonadTraits<MONAD_NEXT>>()});
        }

        void enter_delay(uint64_t const next_epoch)
        {
            staking::StakingContract::Variables staking{state};
            staking.in_epoch_delay_period.store(true);
            ASSERT_TRUE(on_staking_snapshot(state, next_epoch));
        }

        void enter_epoch(uint64_t const epoch)
        {
            staking::StakingContract::Variables staking{state};
            staking.in_epoch_delay_period.store(false);
            staking.epoch.store(u64_be{epoch});
            ASSERT_TRUE(on_staking_epoch_change(state, epoch));
        }
    };

    TEST_F(NativeDkgContractTest, registration_and_pc_qc_are_trie_backed)
    {
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(), validator, uint256_be_t{})
                        .has_value());

        AbiEncoder registration_query;
        registration_query.add_uint(u64_be{2});
        registration_query.add_uint(u64_be{1});
        auto registration = contract.precompile_registration_of(
            registration_query.encode_final(), validator, uint256_be_t{});
        ASSERT_TRUE(registration.has_value());
        ASSERT_EQ(registration.value().size(), 7 * 32);
        EXPECT_EQ(abi_word_u64(registration.value(), 0), 1);
        EXPECT_EQ(abi_word_u64(registration.value(), 2), 3);
        EXPECT_EQ(abi_word_u64(registration.value(), 4), 4);

        AbiEncoder unknown_query;
        unknown_query.add_uint(u64_be{2});
        unknown_query.add_uint(u64_be{2});
        auto unknown_registration = contract.precompile_registration_of(
            unknown_query.encode_final(), validator, uint256_be_t{});
        ASSERT_TRUE(unknown_registration.has_value());
        EXPECT_EQ(abi_word_u64(unknown_registration.value(), 0), 0);

        enter_delay(2);
        ASSERT_TRUE(
            contract
                .precompile_post_pc_qc(pc_qc_call(2), validator, uint256_be_t{})
                .has_value());
        // Repeating the dealer's PC-QC is a no-op; PC markers are keyed only
        // by dealer, because acknowledgements are delivered directly to it.
        ASSERT_TRUE(
            contract
                .precompile_post_pc_qc(pc_qc_call(2), validator, uint256_be_t{})
                .has_value());
        ASSERT_EQ(state.logs().size(), 1);
        EXPECT_EQ(state.logs()[0].address, DKG_CA);
        ASSERT_EQ(state.logs()[0].topics.size(), 4);

        AbiEncoder page_query;
        page_query.add_uint(u64_be{2});
        page_query.add_uint(u64_be{0});
        // Native execution safely caps output work but treats the caller's
        // limit as a maximum instead of rejecting a Solidity-valid request.
        page_query.add_uint(u32_be{100});
        auto page = contract.precompile_pc_qcs(
            page_query.encode_final(), validator, uint256_be_t{});
        ASSERT_TRUE(page.has_value());
        ASSERT_GE(page.value().size(), 13 * 32);
        EXPECT_EQ(abi_word_u64(page.value(), 0), 32); // page tuple offset
        EXPECT_EQ(abi_word_u64(page.value(), 1), 1); // total
        EXPECT_EQ(abi_word_u64(page.value(), 2), 1); // next
        EXPECT_EQ(abi_word_u64(page.value(), 4), 1); // array length
        EXPECT_EQ(abi_word_u64(page.value(), 6), 0); // dealer
        EXPECT_EQ(abi_word_u64(page.value(), 9), 1); // signature count
    }

    TEST_F(NativeDkgContractTest, pc_qc_must_be_posted_by_its_dealer)
    {
        static constexpr Address second_validator =
            0x2222222222222222222222222222222222222222_address;
        staking::StakingContract::Variables staking{state};
        staking.val_id(second_validator).store(u64_be{2});
        staking.valset_consensus.push(u64_be{2});
        staking.consensus_view(u64_be{2}).stake().store(
            u256_be{staking::limits::active_validator_stake<
                MonadTraits<MONAD_NEXT>>()});

        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(), validator, uint256_be_t{})
                        .has_value());
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(), second_validator,
                            uint256_be_t{})
                        .has_value());
        enter_delay(2);

        auto const wrong_dealer = contract.precompile_post_pc_qc(
            pc_qc_call(2, 1), validator, uint256_be_t{});
        ASSERT_TRUE(wrong_dealer.has_error());
        EXPECT_EQ(wrong_dealer.error(), DkgError::NotPcQcDealer);

        ASSERT_TRUE(contract
                        .precompile_post_pc_qc(
                            pc_qc_call(2, 1), second_validator,
                            uint256_be_t{})
                        .has_value());
    }

    TEST_F(NativeDkgContractTest, bve_qc_requires_the_dealers_pc_qc)
    {
        static constexpr Address second_validator =
            0x2222222222222222222222222222222222222222_address;
        staking::StakingContract::Variables staking{state};
        staking.val_id(second_validator).store(u64_be{2});
        staking.valset_consensus.push(u64_be{2});
        staking.consensus_view(u64_be{2}).stake().store(
            u256_be{staking::limits::active_validator_stake<
                MonadTraits<MONAD_NEXT>>()});

        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(), validator, uint256_be_t{})
                        .has_value());
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(), second_validator,
                            uint256_be_t{})
                        .has_value());
        enter_delay(2);

        auto const before_pc = contract.precompile_post_bve_qc(
            bve_qc_call(2, 1), second_validator, uint256_be_t{});
        ASSERT_TRUE(before_pc.has_error());
        EXPECT_EQ(before_pc.error(), DkgError::PcQcRequired);

        ASSERT_TRUE(contract
                        .precompile_post_pc_qc(
                            pc_qc_call(2, 1), second_validator,
                            uint256_be_t{})
                        .has_value());

        auto const wrong_dealer = contract.precompile_post_bve_qc(
            bve_qc_call(2, 1), validator, uint256_be_t{});
        ASSERT_TRUE(wrong_dealer.has_error());
        EXPECT_EQ(wrong_dealer.error(), DkgError::NotBveQcDealer);

        ASSERT_TRUE(contract
                        .precompile_post_bve_qc(
                            bve_qc_call(2, 1), second_validator,
                            uint256_be_t{})
                        .has_value());
        ASSERT_TRUE(contract
                        .precompile_post_bve_qc(
                            bve_qc_call(2, 1), second_validator,
                            uint256_be_t{})
                        .has_value());
        EXPECT_EQ(state.logs().size(), 2);
    }

    TEST_F(
        NativeDkgContractTest,
        reusable_state_slots_isolate_records_and_dedup_by_epoch)
    {
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(2), validator, uint256_be_t{})
                        .has_value());
        enter_delay(2);
        ASSERT_TRUE(
            contract
                .precompile_post_pc_qc(pc_qc_call(2), validator, uint256_be_t{})
                .has_value());

        // Advance twice so epoch 4 reuses the physical slot that held epoch 2.
        // The stale record and dedup marker remain in the trie but belong to an
        // older epoch and must not be visible or suppress a new write.
        enter_epoch(2);
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(3), validator, uint256_be_t{})
                        .has_value());
        enter_delay(3);
        ASSERT_TRUE(
            contract
                .precompile_post_pc_qc(pc_qc_call(3), validator, uint256_be_t{})
                .has_value());

        enter_epoch(3);
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(4), validator, uint256_be_t{})
                        .has_value());
        enter_delay(4);

        AbiEncoder page_query;
        page_query.add_uint(u64_be{4});
        page_query.add_uint(u64_be{0});
        page_query.add_uint(u32_be{16});
        auto empty_page = contract.precompile_pc_qcs(
            page_query.encode_final(), validator, uint256_be_t{});
        ASSERT_TRUE(empty_page.has_value());
        EXPECT_EQ(abi_word_u64(empty_page.value(), 1), 0); // total
        EXPECT_EQ(abi_word_u64(empty_page.value(), 2), 0); // next

        ASSERT_TRUE(
            contract
                .precompile_post_pc_qc(pc_qc_call(4), validator, uint256_be_t{})
                .has_value());
        AbiEncoder populated_query;
        populated_query.add_uint(u64_be{4});
        populated_query.add_uint(u64_be{0});
        populated_query.add_uint(u32_be{16});
        auto populated_page = contract.precompile_pc_qcs(
            populated_query.encode_final(), validator, uint256_be_t{});
        ASSERT_TRUE(populated_page.has_value());
        EXPECT_EQ(abi_word_u64(populated_page.value(), 1), 1); // total
        EXPECT_EQ(abi_word_u64(populated_page.value(), 2), 1); // next
    }

    TEST_F(
        NativeDkgContractTest,
        result_verifies_rust_signature)
    {
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(), validator, uint256_be_t{})
                        .has_value());
        enter_delay(2);

        ASSERT_TRUE(contract
                        .precompile_submit_result(
                            result_call(), validator, uint256_be_t{})
                        .has_value());
        ASSERT_EQ(state.logs().size(), 1);
        EXPECT_EQ(state.logs()[0].address, DKG_CA);
        ASSERT_EQ(state.logs()[0].topics.size(), 2);

        AbiEncoder query;
        query.add_uint(u64_be{2});
        auto recorded = contract.precompile_dkg_result(
            query.encode_final(), validator, uint256_be_t{});
        ASSERT_TRUE(recorded.has_value());
        ASSERT_GE(recorded.value().size(), 26 * 32);
        EXPECT_EQ(abi_word_u64(recorded.value(), 0), 1); // exists
        EXPECT_EQ(abi_word_u64(recorded.value(), 1), 0); // recorded block
        EXPECT_EQ(abi_word_u64(recorded.value(), 23), 1); // signature count
    }

    TEST_F(NativeDkgContractTest, user_call_does_not_repair_epoch_state)
    {
        staking::StakingContract::Variables staking{state};
        staking.epoch.store(u64_be{2});

        auto const unsynchronized = contract.precompile_register(
            registration_call(3), validator, uint256_be_t{});
        ASSERT_TRUE(unsynchronized.has_error());
        EXPECT_EQ(unsynchronized.error(), DkgError::EpochStateUnavailable);

        ASSERT_TRUE(on_staking_epoch_change(state, 2));
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(3), validator, uint256_be_t{})
                        .has_value());
    }

    TEST_F(NativeDkgContractTest, registration_rejects_trailing_calldata)
    {
        byte_string input = registration_call();
        input.push_back(0);
        auto const result =
            contract.precompile_register(input, validator, uint256_be_t{});
        ASSERT_TRUE(result.has_error());
        EXPECT_EQ(result.error(), DkgError::InvalidInput);
    }

    TEST(NativeDkgContract, preloads_direct_storage_owners_after_block_merge)
    {
        vm::VM vm;
        mpt::Db db{std::make_unique<OnDiskMachine>()};
        TrieDb trie_db{db};
        BlockState block_state{trie_db, vm};

        constexpr Address validator =
            0x1111111111111111111111111111111111111111_address;
        {
            State prelude_state{block_state, Incarnation{1, 0}};
            prelude_state.add_to_balance(staking::STAKING_CA, 0);
            staking::StakingContract::Variables staking{prelude_state};
            staking.epoch.store(u64_be{1});
            execute_block_prelude<MonadTraits<MONAD_NEXT>>(prelude_state);
            staking.val_id(validator).store(u64_be{1});
            ASSERT_TRUE(block_state.can_merge(prelude_state));
            block_state.merge(prelude_state);
        }

        // A fresh transaction State has neither storage owner in its local
        // original-account cache. The native contract must make its direct
        // DKG and staking storage reads safe without relying on prior calls.
        State transaction_state{block_state, Incarnation{1, 1}};
        NoopCallTracer call_tracer;
        DkgContract contract{transaction_state, call_tracer};
        auto result = contract.precompile_register(
            registration_call(), validator, uint256_be_t{});
        ASSERT_TRUE(result.has_value());
    }

} // namespace
