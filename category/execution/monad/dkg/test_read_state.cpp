// Copyright (C) 2026 Category Labs, Inc.

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/dkg/dkg_contract.hpp>
#include <category/execution/monad/dkg/execute_block_prelude.hpp>
#include <category/execution/monad/dkg/read_state.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/vm.hpp>

#include <gtest/gtest.h>

#include <unistd.h>

#include <cstring>
#include <memory>
#include <string>
#include <vector>

using namespace monad;
using namespace monad::dkg;
using namespace monad::literals;

namespace
{
    constexpr size_t TEST_BLOCK_NUM = 0;
    constexpr uint64_t TEST_EPOCH = 2;
    constexpr Address VALIDATOR =
        0x1111111111111111111111111111111111111111_address;

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

    byte_string pc_qc_call()
    {
        byte_string result;
        result += abi_encode_uint(u64_be{TEST_EPOCH});
        result += abi_encode_uint(u64_be{64});
        result += abi_encode_uint(u32_be{0});
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

    byte_string bve_qc_call()
    {
        byte_string result;
        result += abi_encode_uint(u64_be{TEST_EPOCH});
        result += abi_encode_uint(u64_be{64});
        result += abi_encode_uint(u32_be{0});
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
        result += abi_encode_uint(u64_be{TEST_EPOCH});
        result += abi_encode_uint(u64_be{64});
        result +=
            0x1111111111111111111111111111111111111111111111111111111111111111_bytes32;
        for (uint64_t i = 1; i <= 18; ++i) {
            result += abi_encode_uint(u64_be{i});
        }
        result += abi_encode_uint(u64_be{20 * 32});
        result += abi_encode_uint(u64_be{1});
        result += abi_encode_uint(u32_be{0});
        result +=
            0x45992c99e5aaa4089a9afdbc3fbc00494a067ab0a73e89ab39684bb56a0a37a8_bytes32;
        result +=
            0x70fd863a84efab09ecc59bd0c6000a8a80a39903f77286d08169671088e9ae7f_bytes32;
        return result;
    }

    struct TempDb
    {
        int fd;
        std::string path;

        TempDb()
            : fd{MONAD_ASYNC_NAMESPACE::make_temporary_inode()}
            , path{"/proc/self/fd/" + std::to_string(fd)}
        {
            MONAD_ASSERT(
                -1 !=
                ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        }

        ~TempDb()
        {
            ::close(fd);
        }
    };
}

TEST(DkgReadState, reads_finalized_native_state_without_eth_call)
{
    TempDb db_file;
    {
        vm::VM vm;
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            mpt::OnDiskDbConfig{.dbname_paths = {db_file.path}}};
        TrieDb trie_db{db};
        BlockState block_state{trie_db, vm};
        State state{block_state, Incarnation{TEST_BLOCK_NUM, 0}};
        NoopCallTracer tracer;

        state.add_to_balance(staking::STAKING_CA, 0);
        staking::StakingContract::Variables staking{state};
        staking.epoch.store(u64_be{1});
        execute_block_prelude<MonadTraits<MONAD_NEXT>>(state);
        staking.val_id(VALIDATOR).store(u64_be{1});
        staking.valset_consensus.push(u64_be{1});
        staking.consensus_view(u64_be{1}).stake().store(
            u256_be{staking::limits::active_validator_stake<
                MonadTraits<MONAD_NEXT>>()});

        DkgContract contract{state, tracer, TEST_BLOCK_NUM};
        ASSERT_TRUE(contract
                        .precompile_register(
                            registration_call(), VALIDATOR, uint256_be_t{})
                        .has_value());
        staking.in_epoch_delay_period.store(true);
        ASSERT_TRUE(on_staking_snapshot(state, TEST_EPOCH));
        ASSERT_TRUE(
            contract
                .precompile_post_pc_qc(pc_qc_call(), VALIDATOR, uint256_be_t{})
                .has_value());
        ASSERT_TRUE(contract
                        .precompile_post_bve_qc(
                            bve_qc_call(), VALIDATOR, uint256_be_t{})
                        .has_value());
        ASSERT_TRUE(contract
                        .precompile_submit_result(
                            result_call(), VALIDATOR, uint256_be_t{})
                        .has_value());

        ASSERT_TRUE(block_state.can_merge(state));
        block_state.merge(state);
        auto [state_deltas, code, _] = std::move(block_state).release();
        test::commit_simple(
            trie_db,
            *state_deltas,
            code,
            NULL_HASH_BLAKE3,
            BlockHeader{.number = TEST_BLOCK_NUM});
        trie_db.finalize(TEST_BLOCK_NUM, NULL_HASH_BLAKE3);
    }

    mpt::AsyncIOContext io_ctx{
        mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {db_file.path}}};
    mpt::Db db{io_ctx};

    auto registrations =
        read_registrations(db, TEST_BLOCK_NUM, TEST_EPOCH, {VALIDATOR});
    ASSERT_TRUE(registrations.has_value());
    EXPECT_FALSE(registrations.value().registration_open);
    ASSERT_EQ(registrations.value().registrations.size(), 1);
    EXPECT_EQ(registrations.value().registrations[0].validator_id, 1u);
    EXPECT_EQ(
        abi_word_u64(registrations.value().registrations[0].registration, 0),
        1);

    auto pc_qcs = read_pc_qcs(db, TEST_BLOCK_NUM, TEST_EPOCH, 0, 16);
    ASSERT_TRUE(pc_qcs.has_value());
    EXPECT_EQ(abi_word_u64(pc_qcs.value(), 1), 1);
    EXPECT_EQ(abi_word_u64(pc_qcs.value(), 2), 1);

    auto bve_qcs = read_bve_qcs(db, TEST_BLOCK_NUM, TEST_EPOCH, 0, 16);
    ASSERT_TRUE(bve_qcs.has_value());
    EXPECT_EQ(abi_word_u64(bve_qcs.value(), 1), 1);
    EXPECT_EQ(abi_word_u64(bve_qcs.value(), 2), 1);

    auto result = read_dkg_result(db, TEST_BLOCK_NUM, TEST_EPOCH);
    ASSERT_TRUE(result.has_value());
    EXPECT_EQ(abi_word_u64(result.value(), 0), 1);
    EXPECT_EQ(abi_word_u64(result.value(), 1), TEST_BLOCK_NUM);
}
