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

#include <category/async/config.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/signature.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/trace/tracer_config.h>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/node_cache.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/rpc/monad_executor.h>
#include <category/vm/code.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>
#include <category/vm/utils/evm-as/validator.hpp>
#include <category/vm/vm.hpp>

#include <test_resource_data.h>

#include <ankerl/unordered_dense.h>

#include <boost/fiber/future/promise.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <gtest/gtest.h>

#include <intx/intx.hpp>

#include <nlohmann/json_fwd.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <deque>
#include <filesystem>
#include <limits>
#include <memory>
#include <optional>
#include <ranges>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <vector>

#include <unistd.h>

using namespace monad;
using namespace monad::test;
using namespace monad::trace;
using namespace monad::literals;

namespace
{
    constexpr uint64_t node_lru_max_mem =
        10240 * mpt::NodeCache::AVERAGE_NODE_SIZE;
    constexpr unsigned max_timeout = std::numeric_limits<unsigned>::max();
    auto const rlp_finalized_id = rlp::encode_bytes32(bytes32_t{});

    auto create_executor(std::string const &dbname)
    {
        monad_executor_pool_config const conf = {1, 2, max_timeout, 1000};
        return monad_executor_create(
            conf, conf, conf, node_lru_max_mem, dbname.c_str());
    }

    std::vector<uint8_t> to_vec(byte_string const &bs)
    {
        std::vector<uint8_t> v{bs.begin(), bs.end()};
        return v;
    }

    struct EthCallFixture : public ::testing::Test
    {
        std::filesystem::path dbname;
        OnDiskMachine machine;
        mpt::Db db;
        TrieDb tdb;
        vm::VM vm;

        EthCallFixture()
            : dbname{[] {
                std::filesystem::path dbname(
                    MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                    "monad_eth_call_test1_XXXXXX");
                int const fd = ::mkstemp((char *)dbname.native().data());
                MONAD_ASSERT(fd != -1);
                MONAD_ASSERT(
                    -1 !=
                    ::ftruncate(
                        fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
                ::close(fd);
                return dbname;
            }()}
            , db{machine,
                 mpt::OnDiskDbConfig{.append = false, .dbname_paths = {dbname}}}
            , tdb{db}
        {
        }

        ~EthCallFixture()
        {
            std::filesystem::remove(dbname);
        }

        void test_transfer_call_with_trace(bool gas_specified);
    };

    struct callback_context
    {
        monad_executor_result *result;
        boost::fibers::promise<void> promise;

        ~callback_context()
        {
            monad_executor_result_release(result);
        }
    };

    void complete_callback(monad_executor_result *result, void *user)
    {
        auto *c = (callback_context *)user;

        c->result = result;
        c->promise.set_value();
    }

    void EthCallFixture::test_transfer_call_with_trace(bool const gas_specified)
    {
        for (uint64_t i = 0; i < 256; ++i) {
            commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
        }

        BlockHeader const header{.number = 256};

        commit_sequential(
            tdb,
            StateDeltas{
                {ADDR_A,
                 StateDelta{
                     .account =
                         {std::nullopt,
                          Account{
                              .balance = 0x200000,
                              .code_hash = NULL_HASH,
                              .nonce = 0x0}}}},
                {ADDR_B,
                 StateDelta{
                     .account =
                         {std::nullopt,
                          Account{.balance = 0, .code_hash = NULL_HASH}}}}},
            Code{},
            header);

        Transaction const tx{
            .max_fee_per_gas = 1,
            .gas_limit = 500'000u,
            .value = 0x10000,
            .to = ADDR_B,
        };
        auto const &from = ADDR_A;

        auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
        auto const rlp_header = to_vec(rlp::encode_block_header(header));
        auto const rlp_sender =
            to_vec(rlp::encode_address(std::make_optional(from)));
        auto const rlp_block_id = to_vec(rlp_finalized_id);

        auto *executor = create_executor(dbname.string());
        auto *state_override = monad_state_override_create();

        struct callback_context ctx;
        boost::fibers::future<void> f = ctx.promise.get_future();

        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)&ctx,
            CALL_TRACER,
            gas_specified);
        f.get();

        EXPECT_EQ(ctx.result->status_code, EVMC_SUCCESS);

        byte_string const rlp_call_frames(
            ctx.result->encoded_trace, ctx.result->encoded_trace_len);
        CallFrame const expected{
            .type = CallType::CALL,
            .flags = 0,
            .from = from,
            .to = ADDR_B,
            .value = 0x10000,
            .gas = gas_specified ? 500'000u : MONAD_ETH_CALL_LOW_GAS_LIMIT,
            .gas_used = gas_specified ? 500'000u : MONAD_ETH_CALL_LOW_GAS_LIMIT,
            .status = EVMC_SUCCESS,
            .depth = 0,
            .logs = std::vector<CallFrame::Log>{},
        };

        byte_string_view view(rlp_call_frames);
        auto const call_frames = rlp::decode_call_frames(view);

        ASSERT_TRUE(call_frames.has_value());
        ASSERT_TRUE(call_frames.value().size() == 1);
        EXPECT_EQ(call_frames.value()[0], expected);

        // The discrepancy between `evmc_result.gas_used` and the `gas_used` in
        // the final CallFrame is expected. This is because Monad currently does
        // not support gas refund — refunds are always zero. As a result, the
        // `gas_used` in the final CallFrame always equals the gas limit.
        // However, `eth_call` returns the actual gas used (not the full gas
        // limit) to ensure `eth_estimateGas` remains usable.
        EXPECT_EQ(ctx.result->gas_refund, 0);
        EXPECT_EQ(ctx.result->gas_used, 21000);

        monad_state_override_destroy(state_override);
        monad_executor_destroy(executor);
    }
}

TEST_F(EthCallFixture, simple_success_call)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction const tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader const header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
    EXPECT_TRUE(ctx.result->encoded_trace_len == 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 21000);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, insufficient_balance)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction const tx{
        .gas_limit = 100000u,
        .value = 1000000000000,
        .to = to,
        .type = TransactionType::eip1559};
    BlockHeader const header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_REJECTED);
    EXPECT_TRUE(std::strcmp(ctx.result->message, "insufficient balance") == 0);
    EXPECT_TRUE(ctx.result->encoded_trace_len == 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 0);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, on_proposed_block)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction const tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader const header{.number = 256};

    tdb.commit({}, {}, bytes32_t{256}, header);
    tdb.set_block_and_prefix(header.number, bytes32_t{256});

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp::encode_bytes32(bytes32_t{256}));

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_SUCCESS);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 21000);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, blockhash_before_fork)
{
    using namespace monad::vm::utils;

    // The behavior in evmc is that, if eip-2935 is
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    constexpr std::array<uint64_t, 7> blockhash_blocks{
        0, 255, 200, 100, 180, 195, 11};
    constexpr size_t output_buffer_size = blockhash_blocks.size() * 32;

    // create a contract which, on init, invokes blockhash
    auto eb = evm_as::prague();
    uint64_t offset = 0;
    for (uint64_t const b : blockhash_blocks) {
        eb.push(b).blockhash().push(offset).mstore();
        offset += 32;
    }
    eb.push(output_buffer_size).push0().return_();

    std::vector<uint8_t> bytecode{};
    ASSERT_TRUE(evm_as::validate(eb));
    evm_as::compile(eb, bytecode);

    Transaction const tx{
        .gas_limit = 100000u,
        .to = std::nullopt,
        .type = TransactionType::eip1559,
        .data = byte_string{bytecode.data(), bytecode.size()}};
    BlockHeader const header{.number = 256};

    tdb.commit({}, {}, bytes32_t{256}, header);
    tdb.set_block_and_prefix(header.number, bytes32_t{256});

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp::encode_bytes32(bytes32_t{256}));

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_SUCCESS);
    ASSERT_EQ(ctx.result->output_data_len, output_buffer_size);

    // BLOCKHASH outputs are packed in a buffer, 32 bytes each. Iterate over and
    // check against expected. note that order matters here.
    uint8_t const *output_ptr = ctx.result->output_data;
    for (uint64_t const b : blockhash_blocks) {
        auto const actual_hash = to_bytes(byte_string_view{output_ptr, 32});
        auto const expected_hash = to_bytes(
            keccak256(rlp::encode_block_header(BlockHeader{.number = b})));
        EXPECT_EQ(actual_hash, expected_hash);
        output_ptr += 32;
    }

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, failed_to_read)
{
    using namespace monad::vm::utils;

    // missing 256 previous blocks
    tdb.reset_root(load_header(nullptr, db, BlockHeader{.number = 1199}), 1199);
    for (uint64_t i = 1200; i < 1256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    // create bytecode that is deployed and calls blockhash on 1000, which is
    // one of the missing blocks
    auto eb = evm_as::prague();
    eb.push(1000).blockhash().push0().mstore().push(0x20).push0().return_();
    std::vector<uint8_t> bytecode{};
    ASSERT_TRUE(evm_as::validate(eb));
    evm_as::compile(eb, bytecode);
    Transaction const tx{
        .gas_limit = 100000u,
        .to = std::nullopt,
        .type = TransactionType::eip1559,
        .data = byte_string{bytecode.data(), bytecode.size()}};
    BlockHeader const header{.number = 1256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_INTERNAL_ERROR);
    EXPECT_STREQ(ctx.result->message, "blockhash: error querying DB");
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 0);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, contract_deployment_success)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from = Address{};

    byte_string const tx_data =
        0x604580600e600039806000f350fe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3_bytes;

    Transaction const tx{.gas_limit = 200000u, .data = tx_data};
    BlockHeader const header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    byte_string const deployed_code_bytes =
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3_bytes;

    std::vector<uint8_t> const deployed_code_vec = {
        deployed_code_bytes.data(),
        deployed_code_bytes.data() + deployed_code_bytes.size()};

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);

    std::vector<uint8_t> const returned_code_vec(
        ctx.result->output_data,
        ctx.result->output_data + ctx.result->output_data_len);
    EXPECT_EQ(returned_code_vec, deployed_code_vec);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 68'137);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, assertion_exception_depth1)
{
    auto const from = ADDR_A;
    auto const to = ADDR_B;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 1, .code_hash = NULL_HASH}}}},
            {to,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = NULL_HASH}}}}},
        Code{},
        BlockHeader{.number = 0});

    Transaction const tx{
        .gas_limit = 21'000u,
        .value = 1,
        .to = to,
        .data = {},
    };

    BlockHeader const header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_INTERNAL_ERROR);
    EXPECT_TRUE(std::strcmp(ctx.result->message, "balance overflow") == 0);
    EXPECT_EQ(ctx.result->output_data_len, 0);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 0);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, assertion_exception_depth2)
{
    auto const addr1 = evmc::address{253};
    auto const addr2 = evmc::address{254};
    auto const addr3 = evmc::address{255};

    EXPECT_EQ(addr3.bytes[19], 255);
    for (size_t i = 0; i < 19; ++i) {
        EXPECT_EQ(addr3.bytes[i], 0);
    }

    // PUSH0
    // PUSH0
    // PUSH0
    // PUSH0
    // PUSH1 2
    // PUSH1 addr3
    // GAS
    // CALL
    auto const code2 = 0x59595959600260FF5AF1_bytes;
    auto const hash2 = to_bytes(keccak256(code2));
    auto const icode2 = vm::make_shared_intercode(code2);

    commit_sequential(
        tdb,
        StateDeltas{
            {addr1,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 1, .code_hash = NULL_HASH}}}},
            {addr2,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 1, .code_hash = hash2}}}},
            {addr3,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max() - 1,
                          .code_hash = NULL_HASH}}}}},
        Code{{hash2, icode2}},
        BlockHeader{.number = 0});

    Transaction const tx{
        .gas_limit = 1'000'000u,
        .value = 1,
        .to = addr2,
        .type = TransactionType::eip1559,
    };

    BlockHeader const header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(addr1)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_INTERNAL_ERROR);
    EXPECT_TRUE(std::strcmp(ctx.result->message, "balance overflow") == 0);
    EXPECT_EQ(ctx.result->output_data_len, 0);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 0);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, loop_out_of_gas)
{
    auto const code = 0x5B5F56_bytes;
    auto const code_hash = to_bytes(keccak256(code));
    auto const icode = monad::vm::make_shared_intercode(code);

    auto const ca = 0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    commit_sequential(
        tdb,
        StateDeltas{
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0x1b58, .code_hash = code_hash}}}}},
        Code{{code_hash, icode}},
        BlockHeader{.number = 0});

    Transaction const tx{.gas_limit = 100000u, .to = ca, .data = {}};

    BlockHeader const header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender = to_vec(rlp::encode_address(std::make_optional(ca)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_OUT_OF_GAS);
    EXPECT_EQ(ctx.result->output_data_len, 0);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 100000u);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, expensive_read_out_of_gas)
{
    auto const code =
        evmc::from_hex(
            "0x60806040526004361061007a575f3560e01c8063c3d0f1d01161004d578063c3"
            "d0f1d014610110578063c7c41c7514610138578063d0e30db014610160578063e7"
            "c9063e1461016a5761007a565b8063209652551461007e57806356cde25b146100"
            "a8578063819eb9bb146100e4578063c252ba36146100fa575b5f5ffd5b34801561"
            "0089575f5ffd5b50610092610194565b60405161009f91906103c0565b60405180"
            "910390f35b3480156100b3575f5ffd5b506100ce60048036038101906100c99190"
            "610407565b61019d565b6040516100db91906104fc565b60405180910390f35b34"
            "80156100ef575f5ffd5b506100f861024c565b005b348015610105575f5ffd5b50"
            "61010e610297565b005b34801561011b575f5ffd5b506101366004803603810190"
            "6101319190610407565b6102ec565b005b348015610143575f5ffd5b5061015e60"
            "04803603810190610159919061051c565b610321565b005b610168610341565b00"
            "5b348015610175575f5ffd5b5061017e61037c565b60405161018b91906103c056"
            "5b60405180910390f35b5f600354905090565b60605f83836101ac919061057456"
            "5b67ffffffffffffffff8111156101c5576101c46105a7565b5b60405190808252"
            "80602002602001820160405280156101f357816020016020820280368337808201"
            "91505090505b5090505f8490505b838110156102415760045f8281526020019081"
            "526020015f2054828281518110610228576102276105d4565b5b60200260200101"
            "818152505080806001019150506101fb565b508091505092915050565b5f61028c"
            "576040517f08c379a0000000000000000000000000000000000000000000000000"
            "0000000081526004016102839061065b565b60405180910390fd5b61162e600181"
            "905550565b5f5f90505b7fffffffffffffffffffffffffffffffffffffffffffff"
            "ffffffffffffffffffff8110156102e95760015460045f83815260200190815260"
            "20015f2081905550808060010191505061029c565b50565b5f8290505b81811015"
            "61031c578060045f8381526020019081526020015f208190555080806001019150"
            "506102f1565b505050565b6002548110610336578060028190555061033e565b80"
            "6003819055505b50565b7fe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c46"
            "0751c2402c5c5cc9109c33346040516103729291906106b8565b60405180910390"
            "a1565b5f607b6003819055505f60ff90505f613039905080825d815c6040518181"
            "52602081602083015e602081f35b5f819050919050565b6103ba816103a8565b82"
            "525050565b5f6020820190506103d35f8301846103b1565b92915050565b5f5ffd"
            "5b6103e6816103a8565b81146103f0575f5ffd5b50565b5f813590506104018161"
            "03dd565b92915050565b5f5f6040838503121561041d5761041c6103d9565b5b5f"
            "61042a858286016103f3565b925050602061043b858286016103f3565b91505092"
            "50929050565b5f81519050919050565b5f82825260208201905092915050565b5f"
            "819050602082019050919050565b610477816103a8565b82525050565b5f610488"
            "838361046e565b60208301905092915050565b5f602082019050919050565b5f61"
            "04aa82610445565b6104b4818561044f565b93506104bf8361045f565b805f5b83"
            "8110156104ef5781516104d6888261047d565b97506104e183610494565b925050"
            "6001810190506104c2565b5085935050505092915050565b5f6020820190508181"
            "035f83015261051481846104a0565b905092915050565b5f602082840312156105"
            "31576105306103d9565b5b5f61053e848285016103f3565b91505092915050565b"
            "7f4e487b7100000000000000000000000000000000000000000000000000000000"
            "5f52601160045260245ffd5b5f61057e826103a8565b9150610589836103a8565b"
            "92508282039050818111156105a1576105a0610547565b5b92915050565b7f4e48"
            "7b71000000000000000000000000000000000000000000000000000000005f5260"
            "4160045260245ffd5b7f4e487b7100000000000000000000000000000000000000"
            "0000000000000000005f52603260045260245ffd5b5f8282526020820190509291"
            "5050565b7f6a7573742074657374696e67206572726f72206d6573736167657300"
            "000000005f82015250565b5f610645601b83610601565b91506106508261061156"
            "5b602082019050919050565b5f6020820190508181035f83015261067281610639"
            "565b9050919050565b5f73ffffffffffffffffffffffffffffffffffffffff8216"
            "9050919050565b5f6106a282610679565b9050919050565b6106b281610698565b"
            "82525050565b5f6040820190506106cb5f8301856106a9565b6106d86020830184"
            "6103b1565b939250505056fea26469706673582212202210aaae8cb738bbb3e073"
            "496288d456725b3fbcf0489d86bd53a8f79be4091764736f6c634300081e0033")
            .value();
    auto const code_hash = to_bytes(keccak256(code));
    auto const icode = monad::vm::make_shared_intercode(code);

    auto const ca = 0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    commit_sequential(
        tdb,
        StateDeltas{
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0x1b58, .code_hash = code_hash}}}}},
        Code{{code_hash, icode}},
        BlockHeader{.number = 0});

    auto const data =
        0x56cde25b00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e20_bytes;
    Transaction const tx{.gas_limit = 30'000'000u, .to = ca, .data = data};

    BlockHeader const header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender = to_vec(rlp::encode_address(std::make_optional(ca)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_OUT_OF_GAS);
    EXPECT_EQ(ctx.result->output_data_len, 0);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 30'000'000u);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, from_contract_account)
{
    using namespace intx;

    auto const code =
        0x6000600155600060025560006003556000600455600060055500_bytes;
    auto const code_hash = to_bytes(keccak256(code));
    auto const icode = monad::vm::make_shared_intercode(code);

    auto const ca = 0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    commit_sequential(
        tdb,
        StateDeltas{
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0x1b58, .code_hash = code_hash}}}}},
        Code{{code_hash, icode}},
        BlockHeader{.number = 0});

    Transaction const tx{
        .gas_limit = 100000u, .to = ca, .data = 0x60025560_bytes};

    BlockHeader const header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender = to_vec(rlp::encode_address(std::make_optional(ca)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        NOOP_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
    EXPECT_EQ(ctx.result->output_data_len, 0);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 62094);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, concurrent_eth_calls)
{
    using namespace intx;

    auto const ca = 0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    for (uint64_t i = 0; i < 300; ++i) {
        if (i == 200) {
            auto const code =
                0x6000600155600060025560006003556000600455600060055500_bytes;
            auto const code_hash = to_bytes(keccak256(code));
            auto const icode = monad::vm::make_shared_intercode(code);

            commit_sequential(
                tdb,
                StateDeltas{
                    {ca,
                     StateDelta{
                         .account =
                             {std::nullopt,
                              Account{
                                  .balance = 0x1b58,
                                  .code_hash = code_hash}}}}},
                Code{{code_hash, icode}},
                BlockHeader{.number = i});
        }
        else {
            commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
        }
    }

    Transaction const tx{
        .gas_limit = 100000u, .to = ca, .data = 0x60025560_bytes};

    auto *executor = create_executor(dbname.string());

    std::deque<std::unique_ptr<callback_context>> ctxs;
    std::deque<boost::fibers::future<void>> futures;
    std::deque<monad_state_override *> state_overrides;

    for (uint64_t b = 200; b < 300; ++b) {
        auto &ctx = ctxs.emplace_back(std::make_unique<callback_context>());
        futures.emplace_back(ctx->promise.get_future());
        auto *const state_override =
            state_overrides.emplace_back(monad_state_override_create());

        BlockHeader const header{.number = b};

        auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
        auto const rlp_header = to_vec(rlp::encode_block_header(header));
        auto const rlp_sender =
            to_vec(rlp::encode_address(std::make_optional(ca)));
        auto const rlp_block_id = to_vec(rlp_finalized_id);

        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)ctx.get(),
            NOOP_TRACER,
            true);
    }

    for (auto [ctx, f, state_override] :
         std::views::zip(ctxs, futures, state_overrides)) {
        f.get();

        EXPECT_TRUE(ctx->result->status_code == EVMC_SUCCESS);
        EXPECT_EQ(ctx->result->output_data_len, 0);
        EXPECT_EQ(ctx->result->encoded_trace_len, 0);
        EXPECT_EQ(ctx->result->gas_refund, 0);
        EXPECT_EQ(ctx->result->gas_used, 62094);

        monad_state_override_destroy(state_override);
    }

    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, transfer_success_with_call_trace)
{
    test_transfer_call_with_trace(true);
}

TEST_F(EthCallFixture, transfer_success_with_trace_unspecified_gas)
{
    test_transfer_call_with_trace(false);
}

TEST_F(EthCallFixture, call_trace_with_logs)
{
    static constexpr auto sender =
        0x00000000000000000000000000000000deadbeef_address;

    // LOG2(2, 1, 0, 0)
    // require(CALL(b_address))
    // require(CALL(c_address))
    // LOG1(3, 0, 0)
    static constexpr auto a_address =
        0x00000000000000000000000000000000aaaaaaaa_address;
    auto const a_code =
        0x600160025f5fa25f5f5f5f5f7300000000000000000000000000000000bbbbbbbb5af115604d575f5f5f5f5f7300000000000000000000000000000000cccccccc5af115604d5760035f5fa1005bfe_bytes;
    auto const a_code_hash = to_bytes(keccak256(a_code));
    auto const a_icode = monad::vm::make_shared_intercode(a_code);

    // CALL(d_address)
    static constexpr auto b_address =
        0x00000000000000000000000000000000bbbbbbbb_address;
    auto const b_code =
        0x5f5f5f5f5f7300000000000000000000000000000000dddddddd5af1_bytes;
    auto const b_code_hash = to_bytes(keccak256(b_code));
    auto const b_icode = monad::vm::make_shared_intercode(b_code);

    // MSTORE(0, 0xFF...FE); LOG1(1, 0, 32)
    static constexpr auto c_address =
        0x00000000000000000000000000000000cccccccc_address;
    auto const c_code = 0x60025f035f52600160205fa1_bytes;
    auto const c_code_hash = to_bytes(keccak256(c_code));
    auto const c_icode = monad::vm::make_shared_intercode(c_code);

    // STOP
    static constexpr auto d_address =
        0x00000000000000000000000000000000dddddddd_address;
    auto const d_code = 0x00_bytes;
    auto const d_code_hash = to_bytes(keccak256(d_code));
    auto const d_icode = monad::vm::make_shared_intercode(d_code);

    commit_sequential(
        tdb,
        StateDeltas{
            {sender,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = NULL_HASH}}}},
            {a_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = a_code_hash}}}},
            {b_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = b_code_hash}}}},
            {c_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = c_code_hash}}}},
            {d_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = d_code_hash}}}}},
        Code{
            {a_code_hash, a_icode},
            {b_code_hash, b_icode},
            {c_code_hash, c_icode},
            {d_code_hash, d_icode},
        },
        BlockHeader{.number = 0});
    BlockHeader const header{.number = 0};

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 100'000,
        .value = 0,
        .to = a_address,
        .data = byte_string{},
    };
    auto const &from = sender;

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();

    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        CALL_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);

    byte_string const rlp_call_frames(
        ctx.result->encoded_trace, ctx.result->encoded_trace_len);

    byte_string_view view(rlp_call_frames);
    auto const call_frames = rlp::decode_call_frames(view);

    ASSERT_TRUE(call_frames.has_value());
    ASSERT_TRUE(call_frames.value().size() == 4);

    auto const sender_to_a = CallFrame{
        .type = CallType::CALL,
        .flags = 0,
        .from = sender,
        .to = a_address,
        .value = 0,
        .gas = 100'000,
        .gas_used = 100'000,
        .input = byte_string{},
        .output = byte_string{},
        .status = EVMC_SUCCESS,
        .depth = 0,
        .logs =
            std::vector{
                CallFrame::Log{
                    .log =
                        {.data = {},
                         .topics =
                             {
                                 intx::be::store<bytes32_t, uint256_t>(2),
                                 intx::be::store<bytes32_t, uint256_t>(1),
                             },
                         .address = a_address},
                    .position = 0,
                },
                CallFrame::Log{
                    .log =
                        {.data = {},
                         .topics =
                             {
                                 intx::be::store<bytes32_t, uint256_t>(3),
                             },
                         .address = a_address},
                    .position = 2,
                },
            },
    };
    EXPECT_EQ(call_frames.value()[0], sender_to_a);

    auto const a_to_b = CallFrame{
        .type = CallType::CALL,
        .flags = 0,
        .from = a_address,
        .to = b_address,
        .value = 0,
        .gas = 66'692,
        .gas_used = 10'115,
        .input = byte_string{},
        .output = byte_string{},
        .status = EVMC_SUCCESS,
        .depth = 1,
        .logs = std::vector<CallFrame::Log>{},
    };
    auto const ab = call_frames.value()[1];
    EXPECT_EQ(call_frames.value()[1], a_to_b);

    auto const b_to_d = CallFrame{
        .type = CallType::CALL,
        .flags = 0,
        .from = b_address,
        .to = d_address,
        .value = 0,
        .gas = 55'693,
        .gas_used = 0,
        .input = byte_string{},
        .output = byte_string{},
        .status = EVMC_SUCCESS,
        .depth = 2,
        .logs = std::vector<CallFrame::Log>{},
    };
    EXPECT_EQ(call_frames.value()[2], b_to_d);

    auto const a_to_c = CallFrame{
        .type = CallType::CALL,
        .flags = 0,
        .from = a_address,
        .to = c_address,
        .value = 0,
        .gas = 46'762,
        .gas_used = 1030,
        .input = byte_string{},
        .output = byte_string{},
        .status = EVMC_SUCCESS,
        .depth = 1,
        .logs = std::vector{CallFrame::Log{
            .log =
                {.data = byte_string{intx::be::store<bytes32_t>(
                     std::numeric_limits<uint256_t>::max() - 1)},
                 .topics = {intx::be::store<bytes32_t, uint256_t>(1)},
                 .address = c_address},
            .position = 0,
        }},
    };
    EXPECT_EQ(call_frames.value()[3], a_to_c);

    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 54'299);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, static_precompile_OOG_with_call_trace)
{
    static constexpr auto precompile_address{
        0x0000000000000000000000000000000000000001_address};
    static constexpr std::string s = "hello world";
    byte_string_view const data = to_byte_string_view(s);

    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    BlockHeader const header{.number = 256};

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 22000,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {precompile_address,
             StateDelta{.account = {std::nullopt, Account{.nonce = 6}}}}},
        Code{},
        header);

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 22000, // bigger than intrinsic_gas, but smaller than
                            // intrinsic_gas + 3000 (precompile gas)
        .value = 0,
        .to = precompile_address,
        .data = byte_string(data),
    };
    auto const &from = ADDR_A;

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();

    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        CALL_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_OUT_OF_GAS);

    byte_string const rlp_call_frames(
        ctx.result->encoded_trace, ctx.result->encoded_trace_len);

    CallFrame const expected{
        .type = CallType::CALL,
        .flags = 0,
        .from = from,
        .to = precompile_address,
        .value = 0,
        .gas = 22000,
        .gas_used = 22000,
        .input = byte_string(data),
        .status = EVMC_OUT_OF_GAS,
        .depth = 0,
        .logs = std::vector<CallFrame::Log>{},
    };

    byte_string_view view(rlp_call_frames);
    auto const call_frames = rlp::decode_call_frames(view);

    ASSERT_TRUE(call_frames.has_value());
    ASSERT_TRUE(call_frames.value().size() == 1);
    EXPECT_EQ(call_frames.value()[0], expected);

    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 22000);

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

// Same setup as transfer_success_with_call_trace, include both prestate &
// statedelta trace checks
TEST_F(EthCallFixture, transfer_success_with_state_trace)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    BlockHeader const header{.number = 256};

    Account const acct_from{
        .balance = 0x200000,
        .code_hash = NULL_HASH,
        .nonce = 0x0,
    };

    Account const acct_to{};

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A, StateDelta{.account = {std::nullopt, acct_from}}},
            {ADDR_B, StateDelta{.account = {std::nullopt, acct_to}}}},
        Code{},
        header);

    BlockState bs{tdb, this->vm};
    State s{bs, Incarnation{0, 0}};

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 500'000u,
        .value = 0x10000,
        .to = ADDR_B,
    };
    auto const &from = ADDR_A;

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context prestate_ctx;
    struct callback_context statediff_ctx;

    // PreState
    {
        boost::fibers::future<void> f = prestate_ctx.promise.get_future();

        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)&prestate_ctx,
            PRESTATE_TRACER,
            true);
        f.get();

        ASSERT_EQ(prestate_ctx.result->status_code, EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_pre_state_trace(
            prestate_ctx.result->encoded_trace,
            prestate_ctx.result->encoded_trace +
                prestate_ctx.result->encoded_trace_len);
        trace::Map<Address, OriginalAccountState> expected{};
        {
            OriginalAccountState const as_from{acct_from};
            expected.emplace(ADDR_A, as_from);

            OriginalAccountState const as_to{acct_to};
            expected.emplace(ADDR_B, as_to);

            OriginalAccountState const as_bene{std::nullopt};
            expected.emplace(header.beneficiary, as_bene);
        }

        EXPECT_EQ(
            state_to_json(expected, s),
            nlohmann::json::from_cbor(encoded_pre_state_trace));
    }

    // StateDelta
    {
        boost::fibers::future<void> f = statediff_ctx.promise.get_future();

        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)&statediff_ctx,
            STATEDIFF_TRACER,
            true);
        f.get();

        ASSERT_EQ(statediff_ctx.result->status_code, EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_state_delta_trace(
            statediff_ctx.result->encoded_trace,
            statediff_ctx.result->encoded_trace +
                statediff_ctx.result->encoded_trace_len);

        // monad charges gas_limit
        StateDeltas const expected = StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {Account{.balance = 0x200000, .nonce = 0},
                      Account{
                          .balance = 0x200000 - 0x10000 - 500'000u,
                          .nonce = 1}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {Account{.balance = 0, .nonce = 0},
                      Account{.balance = 0x10000}}}},
        };

        EXPECT_EQ(
            state_deltas_to_json(expected, s),
            nlohmann::json::from_cbor(encoded_state_delta_trace));
    }

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

// same setup as contract_deployment_success, but with prestate and statediff
// tracer
TEST_F(EthCallFixture, contract_deployment_success_with_state_trace)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from = Address{};

    byte_string const tx_data =
        0x604580600e600039806000f350fe7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3_bytes;

    Transaction const tx{.gas_limit = 200000u, .data = tx_data};
    BlockHeader const header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    byte_string deployed_code_bytes =
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3_bytes;

    std::vector<uint8_t> const deployed_code_vec = {
        deployed_code_bytes.data(),
        deployed_code_bytes.data() + deployed_code_bytes.size()};

    struct callback_context prestate_ctx;
    struct callback_context statediff_ctx;

    // PreState trace
    {
        boost::fibers::future<void> f = prestate_ctx.promise.get_future();
        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)&prestate_ctx,
            PRESTATE_TRACER,
            true);
        f.get();

        ASSERT_TRUE(prestate_ctx.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_pre_state_trace(
            prestate_ctx.result->encoded_trace,
            prestate_ctx.result->encoded_trace +
                prestate_ctx.result->encoded_trace_len);

        auto const *const expected = R"({
            "0x0000000000000000000000000000000000000000":{"balance":"0x0"},
            "0xbd770416a3345f91e4b34576cb804a576fa48eb1":{"balance":"0x0"}
        })";
        EXPECT_EQ(
            nlohmann::json::parse(expected),
            nlohmann::json::from_cbor(encoded_pre_state_trace));
    }

    // StateDelta Trace
    {
        boost::fibers::future<void> f = statediff_ctx.promise.get_future();
        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)&statediff_ctx,
            STATEDIFF_TRACER,
            true);
        f.get();

        ASSERT_TRUE(statediff_ctx.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_state_deltas_trace(
            statediff_ctx.result->encoded_trace,
            statediff_ctx.result->encoded_trace +
                statediff_ctx.result->encoded_trace_len);

        auto const *const expected = R"({
            "post":{
                "0x0000000000000000000000000000000000000000":{
                    "balance":"0x0",
                    "nonce":1
                },
                "0xbd770416a3345f91e4b34576cb804a576fa48eb1":{
                    "balance":"0x0",
                    "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3",
                    "nonce":1
                }
            },
            "pre":{}
        })";

        EXPECT_EQ(
            nlohmann::json::parse(expected),
            nlohmann::json::from_cbor(encoded_state_deltas_trace));
    }

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, trace_block_with_prestate)
{
    static constexpr Address ADDR_A =
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_address;
    {
        // Initial state.
        StateDeltas const deltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = uint256_t{uint64_t{0x01}}, .nonce = 1}}}},
        };

        commit_sequential(tdb, deltas, {}, BlockHeader{.number = 0});
    }

    // Advance to block 256
    for (uint64_t i = 1; i < 255; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    // Setup block 256 transactions. Before committing them, we setup the
    // transaction senders and put them in block 255.
    auto const next_sig = [&]() -> SignatureAndChain {
        static uint64_t r = 1;
        MonadDevnet const devnet;
        return SignatureAndChain{r++, 1, devnet.get_chain_id(), 1};
    };

    auto const make_tx = [&]() -> Transaction {
        static uint64_t next_tx_nonce = 1;

        Transaction tx;
        tx.gas_limit = 200000u;
        tx.nonce = next_tx_nonce++;
        tx.to = ADDR_A;
        tx.sc = next_sig();
        tx.value = uint256_t{uint64_t{0xABBA}};
        return tx;
    };
    std::vector<Transaction> const transactions = {make_tx(), make_tx()};

    std::vector<Address> senders{};
    StateDeltas senders_state{};
    for (auto const &transaction : transactions) {
        auto const sender = recover_sender(transaction);
        ASSERT_TRUE(sender.has_value());
        senders.push_back(*sender);
        senders_state.emplace(
            *sender,
            StateDelta{
                .account = {
                    std::nullopt,
                    Account{
                        .balance = std::numeric_limits<uint256_t>::max(),
                        .nonce = transaction.nonce}}});
    }
    commit_sequential(tdb, senders_state, {}, BlockHeader{.number = 255});

    // Now commit block 256.
    BlockHeader const header{.number = 256};
    std::vector<Receipt> const receipts = {
        Receipt{.status = EVMC_SUCCESS, .gas_used = 20000u},
        Receipt{.status = EVMC_SUCCESS, .gas_used = 20000u}};

    std::vector<std::vector<CallFrame>> const call_frames = {{}, {}};

    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_block_id = to_vec(rlp_finalized_id);
    auto const rlp_parent_id = to_vec(rlp::encode_bytes32(bytes32_t{255}));
    auto const rlp_grandparent_id = to_vec(rlp::encode_bytes32(bytes32_t{254}));

    commit_sequential(
        tdb,
        {},
        {},
        BlockHeader{.number = 256},
        receipts,
        call_frames,
        senders,
        transactions);

    auto *executor = create_executor(dbname.string());

    struct callback_context prestate_ctx;
    struct callback_context statediff_ctx;

    // PreState trace
    {
        boost::fibers::future<void> f = prestate_ctx.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            256,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            -1,
            complete_callback,
            (void *)&prestate_ctx,
            PRESTATE_TRACER);
        f.get();

        ASSERT_TRUE(prestate_ctx.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_pre_state_trace(
            prestate_ctx.result->encoded_trace,
            prestate_ctx.result->encoded_trace +
                prestate_ctx.result->encoded_trace_len);

        auto const *const expected = R"([
            {
                "result": {
                    "0x0000000000000000000000000000000000000000": {
                        "balance": "0x0"
                    },
                    "0x4bbec6f9d3d530b49a622955e402a87adcbe99c2": {
                        "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                        "nonce": 1
                    },
                    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                        "balance": "0x1",
                        "nonce": 1
                    }
                },
                "txHash": "0x659b50d5b5c543fb681ace210eb175938d5b829297bcf579bc186ac0ea0874dd"
            },
            {
                "result": {
                    "0x0000000000000000000000000000000000000000": {
                        "balance": "0x0"
                    },
                    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                        "balance": "0xabbb",
                        "nonce": 1
                    },
                    "0xc48513273d60b70ee2f25d5c4256612a91573e1e": {
                        "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                        "nonce": 2
                    }
                },
                "txHash": "0x0b391cd83e5ebd2a5d5c0223c4258eaa364737cc6cb9f88c83eced5eb2543e8b"
            }
        ])";
        EXPECT_EQ(
            nlohmann::json::parse(expected),
            nlohmann::json::from_cbor(encoded_pre_state_trace));
    }

    // StateDelta Trace
    {
        boost::fibers::future<void> f = statediff_ctx.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            256,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            -1,
            complete_callback,
            (void *)&statediff_ctx,
            STATEDIFF_TRACER);
        f.get();

        ASSERT_TRUE(statediff_ctx.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_state_diff_trace(
            statediff_ctx.result->encoded_trace,
            statediff_ctx.result->encoded_trace +
                statediff_ctx.result->encoded_trace_len);

        auto const *const expected = R"([
            {
                "result": {
                    "post": {
                        "0x4bbec6f9d3d530b49a622955e402a87adcbe99c2": {
                            "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5445",
                            "nonce": 2
                        },
                        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                            "balance": "0xabbb"
                        }
                    },
                    "pre": {
                        "0x4bbec6f9d3d530b49a622955e402a87adcbe99c2": {
                            "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                            "nonce": 1
                        },
                        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                            "balance": "0x1",
                            "nonce": 1
                        }
                    }
                },
                "txHash": "0x659b50d5b5c543fb681ace210eb175938d5b829297bcf579bc186ac0ea0874dd"
            },
            {
                "result": {
                    "post": {
                        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                            "balance": "0x15775"
                        },
                        "0xc48513273d60b70ee2f25d5c4256612a91573e1e": {
                            "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5445",
                            "nonce": 3
                        }
                    },
                    "pre": {
                        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                            "balance": "0xabbb",
                            "nonce": 1
                        },
                        "0xc48513273d60b70ee2f25d5c4256612a91573e1e": {
                            "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                            "nonce": 2
                        }
                    }
                },
                "txHash": "0x0b391cd83e5ebd2a5d5c0223c4258eaa364737cc6cb9f88c83eced5eb2543e8b"
            }
        ])";
        EXPECT_EQ(
            nlohmann::json::parse(expected),
            nlohmann::json::from_cbor(encoded_state_diff_trace));
    }

    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, trace_transaction_with_prestate)
{
    static constexpr Address ADDR_A =
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_address;
    {
        // Initial state.
        StateDeltas const deltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = uint256_t{uint64_t{0x01}}, .nonce = 1}}}},
        };

        commit_sequential(tdb, deltas, {}, BlockHeader{.number = 0});
    }

    // Advance to block 256
    for (uint64_t i = 1; i < 255; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    // Setup block 256 transactions. Before committing them, we setup the
    // transaction senders and put them in block 255.
    auto const next_sig = [&]() -> SignatureAndChain {
        static uint64_t r = 1;
        MonadDevnet const devnet;
        return SignatureAndChain{r++, 1, devnet.get_chain_id(), 1};
    };

    auto const make_tx = [&]() -> Transaction {
        static uint64_t next_tx_nonce = 1;

        Transaction tx;
        tx.gas_limit = 200000u;
        tx.nonce = next_tx_nonce++;
        tx.to = ADDR_A;
        tx.sc = next_sig();
        tx.value = uint256_t{uint64_t{0xABBA}};
        return tx;
    };
    std::vector<Transaction> const transactions = {make_tx(), make_tx()};

    std::vector<Address> senders{};
    StateDeltas senders_state{};
    for (auto const &transaction : transactions) {
        auto const sender = recover_sender(transaction);
        ASSERT_TRUE(sender.has_value());
        senders.push_back(*sender);
        senders_state.emplace(
            *sender,
            StateDelta{
                .account = {
                    std::nullopt,
                    Account{
                        .balance = std::numeric_limits<uint256_t>::max(),
                        .nonce = transaction.nonce}}});
    }
    commit_sequential(tdb, senders_state, {}, BlockHeader{.number = 255});

    // Now commit block 256.
    BlockHeader const header{.number = 256};
    std::vector<Receipt> const receipts = {
        Receipt{.status = EVMC_SUCCESS, .gas_used = 20000u},
        Receipt{.status = EVMC_SUCCESS, .gas_used = 20000u}};

    std::vector<std::vector<CallFrame>> const call_frames = {{}, {}};

    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_block_id = to_vec(rlp_finalized_id);
    auto const rlp_parent_id = to_vec(rlp::encode_bytes32(bytes32_t{255}));
    auto const rlp_grandparent_id = to_vec(rlp::encode_bytes32(bytes32_t{254}));

    commit_sequential(
        tdb,
        {},
        {},
        BlockHeader{.number = 256},
        receipts,
        call_frames,
        senders,
        transactions);

    auto *executor = create_executor(dbname.string());

    struct callback_context prestate_ctx_1;
    struct callback_context prestate_ctx_2;
    struct callback_context statediff_ctx_1;
    struct callback_context statediff_ctx_2;

    // PreState trace
    {
        boost::fibers::future<void> f_1 = prestate_ctx_1.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            256,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            0,
            complete_callback,
            (void *)&prestate_ctx_1,
            PRESTATE_TRACER);
        f_1.get();

        ASSERT_TRUE(prestate_ctx_1.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_pre_state_trace_1(
            prestate_ctx_1.result->encoded_trace,
            prestate_ctx_1.result->encoded_trace +
                prestate_ctx_1.result->encoded_trace_len);

        auto const *const expected_1 = R"(
            {
                "result": {
                    "0x0000000000000000000000000000000000000000": {
                        "balance": "0x0"
                    },
                    "0x4bbec6f9d3d530b49a622955e402a87adcbe99c2": {
                        "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                        "nonce": 1
                    },
                    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                        "balance": "0x1",
                        "nonce": 1
                    }
                },
                "txHash": "0x659b50d5b5c543fb681ace210eb175938d5b829297bcf579bc186ac0ea0874dd"
            })";

        EXPECT_EQ(
            nlohmann::json::parse(expected_1),
            nlohmann::json::from_cbor(encoded_pre_state_trace_1));

        boost::fibers::future<void> f_2 = prestate_ctx_2.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            256,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            1,
            complete_callback,
            (void *)&prestate_ctx_2,
            PRESTATE_TRACER);
        f_2.get();

        ASSERT_TRUE(prestate_ctx_2.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_pre_state_trace_2(
            prestate_ctx_2.result->encoded_trace,
            prestate_ctx_2.result->encoded_trace +
                prestate_ctx_2.result->encoded_trace_len);

        auto const *const expected_2 = R"(
        {
                "result": {
                    "0x0000000000000000000000000000000000000000": {
                        "balance": "0x0"
                    },
                    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                        "balance": "0xabbb",
                        "nonce": 1
                    },
                    "0xc48513273d60b70ee2f25d5c4256612a91573e1e": {
                        "balance":
                        "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                        "nonce": 2
                    }
                },
                "txHash": "0x0b391cd83e5ebd2a5d5c0223c4258eaa364737cc6cb9f88c83eced5eb2543e8b"
            })";
        EXPECT_EQ(
            nlohmann::json::parse(expected_2),
            nlohmann::json::from_cbor(encoded_pre_state_trace_2));
    }

    // StateDelta Trace
    {
        boost::fibers::future<void> f_1 = statediff_ctx_1.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            256,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            0,
            complete_callback,
            (void *)&statediff_ctx_1,
            STATEDIFF_TRACER);
        f_1.get();

        ASSERT_TRUE(statediff_ctx_1.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_state_diff_trace_1(
            statediff_ctx_1.result->encoded_trace,
            statediff_ctx_1.result->encoded_trace +
                statediff_ctx_1.result->encoded_trace_len);

        auto const *const expected_1 = R"({
                "result": {
                    "post": {
                        "0x4bbec6f9d3d530b49a622955e402a87adcbe99c2": {
                            "balance":
                            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5445",
                            "nonce": 2
                        },
                        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                            "balance": "0xabbb"
                        }
                    },
                    "pre": {
                        "0x4bbec6f9d3d530b49a622955e402a87adcbe99c2": {
                            "balance":
                            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                            "nonce": 1
                        },
                        "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                            "balance": "0x1",
                            "nonce": 1
                        }
                    }
                },
                "txHash": "0x659b50d5b5c543fb681ace210eb175938d5b829297bcf579bc186ac0ea0874dd"
            })";

        EXPECT_EQ(
            nlohmann::json::parse(expected_1),
            nlohmann::json::from_cbor(encoded_state_diff_trace_1));

        boost::fibers::future<void> f_2 = statediff_ctx_2.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            256,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            1,
            complete_callback,
            (void *)&statediff_ctx_2,
            STATEDIFF_TRACER);
        f_2.get();

        ASSERT_TRUE(statediff_ctx_2.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_state_diff_trace_2(
            statediff_ctx_2.result->encoded_trace,
            statediff_ctx_2.result->encoded_trace +
                statediff_ctx_2.result->encoded_trace_len);

        auto const *const expected_2 = R"({
            "result": {
                "post": {
                    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                        "balance": "0x15775"
                    },
                    "0xc48513273d60b70ee2f25d5c4256612a91573e1e": {
                        "balance":
                        "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5445",
                        "nonce": 3
                    }
                },
                "pre": {
                    "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                        "balance": "0xabbb",
                        "nonce": 1
                    },
                    "0xc48513273d60b70ee2f25d5c4256612a91573e1e": {
                        "balance":
                        "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                        "nonce": 2
                    }
                }
            },
            "txHash":
            "0x0b391cd83e5ebd2a5d5c0223c4258eaa364737cc6cb9f88c83eced5eb2543e8b"
        })";

        EXPECT_EQ(
            nlohmann::json::parse(expected_2),
            nlohmann::json::from_cbor(encoded_state_diff_trace_2));
    }

    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, monad_executor_run_reserve_balance)
{
    // This test is ported from `test_monad_chain.cpp` (reserve balance). It
    // triggers the case where the sender is both in the parent block and the
    // current block, with an emptying transaction.
    static constexpr uint256_t BASE_FEE_PER_GAS = 10;

    // Parameters
    uint64_t const initial_balance_mon = 10;
    uint64_t const gas_fee_mon = 2;
    uint64_t const value_mon = 1;
    uint256_t const value = uint256_t{value_mon} * 1000000000000000000ULL;
    uint256_t const gas_fee = uint256_t{gas_fee_mon} * 1000000000000000000ULL;
    uint256_t const gas_limit_ = gas_fee / BASE_FEE_PER_GAS;
    ASSERT_TRUE((gas_fee % BASE_FEE_PER_GAS) == 0);
    ASSERT_TRUE(gas_limit_ <= std::numeric_limits<uint64_t>::max());
    uint64_t const gas_limit = static_cast<uint64_t>(gas_limit_);

    // We need transactions to validate, hence we need an address and a
    // signature. We can retrieve the former from the latter by first
    // constructing the transaction, sign it, and then run `recover_sender` on
    // it.
    auto const sig = [&]() -> SignatureAndChain {
        MonadDevnet const devnet;
        return SignatureAndChain{1, 1, devnet.get_chain_id(), 1};
    }();

    Transaction const tx{
        .sc = sig,
        .nonce = 1,
        .max_fee_per_gas = BASE_FEE_PER_GAS,
        .gas_limit = gas_limit,
        .value = value,
        .type = TransactionType::legacy,
        .max_priority_fee_per_gas = 0,
    };

    Address const sender = recover_sender(tx).value();
    Account const sender_acc{
        .balance = uint256_t{initial_balance_mon} * 1000000000000000000ULL,
        .nonce = 1};
    {
        // Initial state.
        StateDeltas const deltas{
            {
                sender,
                StateDelta{.account = {std::nullopt, sender_acc}},
            },
        };

        commit_sequential(tdb, deltas, {}, BlockHeader{.number = 0});
    }

    // Advance to block 255
    for (uint64_t i = 1; i < 254; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    // Setup parent block transactions.
    Account sender_acc2 = sender_acc;
    sender_acc2.nonce = 1;
    {
        Transaction const tx0{
            .sc = sig,
            .nonce = 1,
            .max_fee_per_gas = BASE_FEE_PER_GAS,
            .gas_limit = gas_limit,
            .value = value,
            .type = TransactionType::legacy,
            .max_priority_fee_per_gas = 0,
        };

        ASSERT_EQ(sender, recover_sender(tx0).value());

        std::vector<Transaction> const transactions = {tx0};
        std::vector<Address> const senders = {sender};
        std::vector<std::vector<std::optional<Address>>> const authorities = {
            {}};
        std::vector<Receipt> const receipts = {{}};
        std::vector<std::vector<CallFrame>> const call_frames = {{}};

        BlockHeader const header{
            .number = 254,
            .timestamp = MONAD_NEXT,
            .base_fee_per_gas = BASE_FEE_PER_GAS};

        commit_sequential(
            tdb,
            StateDeltas{
                {
                    sender,
                    StateDelta{.account = {sender_acc, sender_acc2}},
                },
            },
            {},
            header,
            receipts,
            call_frames,
            senders,
            transactions);
    }
    // Setup target block transactions.
    std::vector<Transaction> const transactions = {tx};
    std::vector<Address> const senders = {sender};
    std::vector<std::vector<std::optional<Address>>> const authorities = {{}};
    std::vector<Receipt> const receipts = {{}};
    std::vector<std::vector<CallFrame>> const call_frames = {{}};

    BlockHeader const header{
        .number = 255,
        .timestamp = MONAD_NEXT,
        .base_fee_per_gas = BASE_FEE_PER_GAS};

    Account sender_acc3 = sender_acc2;
    sender_acc3.nonce += 1;

    commit_sequential(
        tdb,
        StateDeltas{
            {
                sender,
                StateDelta{.account = {sender_acc2, sender_acc3}},
            },
        },
        {},
        header,
        receipts,
        call_frames,
        senders,
        transactions);

    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_block_id = to_vec(rlp_finalized_id);
    auto const rlp_parent_id = to_vec(rlp::encode_bytes32(bytes32_t{}));
    auto const rlp_grandparent_id = to_vec(rlp::encode_bytes32(bytes32_t{}));

    {
        // Simulate the transaction to verify that it indeed should revert.
        ankerl::unordered_dense::segmented_set<Address> const
            grandparent_senders_and_authorities;
        ankerl::unordered_dense::segmented_set<Address> const
            parent_senders_and_authorities = {sender};
        ankerl::unordered_dense::segmented_set<Address> const
            senders_and_authorities = {sender};
        MonadChainContext const chain_context{
            .grandparent_senders_and_authorities =
                &grandparent_senders_and_authorities,
            .parent_senders_and_authorities = &parent_senders_and_authorities,
            .senders_and_authorities = senders_and_authorities,
            .senders = senders,
            .authorities = authorities};

        BlockState block_state{tdb, vm};
        State state{
            block_state, Incarnation{header.number - 1, Incarnation::LAST_TX}};
        state.subtract_from_balance(sender, gas_fee);
        state.subtract_from_balance(sender, value);
        EXPECT_TRUE(block_state.can_merge(state));
        bool const should_revert = revert_monad_transaction(
            MONAD_NEXT,
            EVMC_PRAGUE,
            sender,
            tx,
            BASE_FEE_PER_GAS,
            0, // transaction index
            state,
            chain_context);
        EXPECT_TRUE(should_revert);
    }

    auto *executor = create_executor(dbname.string());

    struct callback_context statediff_ctx_1;

    // StateDiff trace
    {
        boost::fibers::future<void> f_1 = statediff_ctx_1.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            0,
            complete_callback,
            (void *)&statediff_ctx_1,
            STATEDIFF_TRACER);
        f_1.get();

        // TODO(dhil): this should really be EMVC_REVERT, but currently
        // `monad_executor` returns `EVMC_SUCCESS` if the `Result`-object
        // returned by `execute_transaction` is constructed using the success
        // constructor.
        EXPECT_EQ(statediff_ctx_1.result->status_code, EVMC_SUCCESS)
            << statediff_ctx_1.result->message;

        std::vector<uint8_t> const encoded_state_diff_trace_1(
            statediff_ctx_1.result->encoded_trace,
            statediff_ctx_1.result->encoded_trace +
                statediff_ctx_1.result->encoded_trace_len);

        auto const *const expected_1 = R"({
            "result": {
                "post": {
                    "0x4ae670ab7f6f092aae0411169e47c482a1fd262b": {
                        "balance": "0x6f05b59d3b200000",
                        "nonce": 2
                    }
                },
                "pre": {
                    "0x4ae670ab7f6f092aae0411169e47c482a1fd262b": {
                        "balance": "0x8ac7230489e80000",
                        "nonce": 1
                    }
                }
            },
            "txHash": "0x5b341e8b3055bb33a13628668721a76a1829197e37c34c299fe77dbf7e877423"
        })";

        EXPECT_EQ(
            nlohmann::json::parse(expected_1),
            nlohmann::json::from_cbor(encoded_state_diff_trace_1));
    }

    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, prestate_trace_near_genesis)
{
    static constexpr Address ADDR_A =
        0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa_address;

    auto const next_sig = [&]() -> SignatureAndChain {
        static uint64_t r = 1;
        MonadDevnet const devnet;
        return SignatureAndChain{r++, 1, devnet.get_chain_id(), 1};
    };

    Transaction const block1_tx{
        .sc = next_sig(),
        .nonce = 1,
        .gas_limit = 21000,
        .value = uint256_t{uint64_t{0x01}},
        .to = ADDR_A,
    };

    Transaction const block2_tx{
        .sc = next_sig(),
        .nonce = 1,
        .gas_limit = 42000,
        .value = uint256_t{uint64_t{0xAA}},
        .to = ADDR_A,
    };

    auto const block1_tx_sender = recover_sender(block1_tx).value();
    auto const block2_tx_sender = recover_sender(block2_tx).value();

    {
        // Initial state.
        StateDeltas const deltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = uint256_t{uint64_t{0x01}}, .nonce = 1}}}},
            {block1_tx_sender,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .nonce = block1_tx.nonce}}}},
            {block2_tx_sender,
             StateDelta{
                 .account = {
                     std::nullopt,
                     Account{
                         .balance =
                             uint256_t{std::numeric_limits<uint64_t>::max()},
                         .nonce = block2_tx.nonce}}}}};

        commit_sequential(tdb, deltas, {}, BlockHeader{.number = 0});
    }

    // Genesis block
    BlockHeader const header{.number = 0};
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_block_id = to_vec(rlp_finalized_id);
    auto const rlp_parent_id = to_vec(rlp::encode_bytes32(bytes32_t{}));
    auto const rlp_grandparent_id = to_vec(rlp::encode_bytes32(bytes32_t{}));

    auto *executor = create_executor(dbname.string());

    struct callback_context genesis_prestate_ctx;
    {
        boost::fibers::future<void> f =
            genesis_prestate_ctx.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            0,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            -1,
            complete_callback,
            (void *)&genesis_prestate_ctx,
            PRESTATE_TRACER);
        f.get();

        ASSERT_TRUE(genesis_prestate_ctx.result->status_code == EVMC_REJECTED);

        char const *const expected_message = "cannot trace genesis block";

        EXPECT_TRUE(
            std::strcmp(
                genesis_prestate_ctx.result->message, expected_message) == 0);
    }

    // Block 1
    struct callback_context block1_prestate_ctx;
    {
        std::vector<Transaction> const transactions = {block1_tx};
        std::vector<Address> const senders = {block1_tx_sender};
        std::vector<Receipt> const receipts = {{}};
        std::vector<std::vector<CallFrame>> const call_frames = {{}};

        BlockHeader const header{.number = 1};
        auto const rlp_header = to_vec(rlp::encode_block_header(header));

        commit_sequential(
            tdb, {}, {}, header, receipts, call_frames, senders, transactions);

        boost::fibers::future<void> f =
            block1_prestate_ctx.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            0,
            complete_callback,
            (void *)&block1_prestate_ctx,
            PRESTATE_TRACER);
        f.get();

        ASSERT_TRUE(block1_prestate_ctx.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_pre_state_trace(
            block1_prestate_ctx.result->encoded_trace,
            block1_prestate_ctx.result->encoded_trace +
                block1_prestate_ctx.result->encoded_trace_len);

        auto const *const expected = R"({
            "result": {
                "0x0000000000000000000000000000000000000000": {
                    "balance": "0x0"
                },
                "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                    "balance": "0x1",
                    "nonce": 1
                },
                "0xbedcab535cc48a9bd659ac448f092d02ba23a05a": {
                    "balance": "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
                    "nonce":1
                }
            },
            "txHash": "0x1618c6e833ab2d6a9574982709de8c7d88da1851c5bd2ca8e31c0e43ead8647b"
        })";
        EXPECT_EQ(
            nlohmann::json::parse(expected),
            nlohmann::json::from_cbor(encoded_pre_state_trace));
    }

    // Block 2
    struct callback_context block2_prestate_ctx;
    {
        std::vector<Transaction> const transactions = {block2_tx};
        std::vector<Address> const senders = {block2_tx_sender};
        std::vector<Receipt> const receipts = {{}};
        std::vector<std::vector<CallFrame>> const call_frames = {{}};

        BlockHeader const header{.number = 2};
        auto const rlp_header = to_vec(rlp::encode_block_header(header));

        commit_sequential(
            tdb, {}, {}, header, receipts, call_frames, senders, transactions);

        boost::fibers::future<void> f =
            block2_prestate_ctx.promise.get_future();
        monad_executor_run_transactions(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_header.data(),
            rlp_header.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            rlp_parent_id.data(),
            rlp_parent_id.size(),
            rlp_grandparent_id.data(),
            rlp_grandparent_id.size(),
            0,
            complete_callback,
            (void *)&block2_prestate_ctx,
            PRESTATE_TRACER);
        f.get();

        ASSERT_TRUE(block2_prestate_ctx.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_pre_state_trace(
            block2_prestate_ctx.result->encoded_trace,
            block2_prestate_ctx.result->encoded_trace +
                block2_prestate_ctx.result->encoded_trace_len);

        auto const *const expected = R"({
            "result": {
                "0x0000000000000000000000000000000000000000": {
                    "balance": "0x0"
                },
                "0xa6b8a0d6cbd7623be3a45d2164c436e6d3462d99": {
                    "balance": "0xffffffffffffffff",
                    "nonce": 1
                },
                "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa": {
                    "balance": "0x1",
                    "nonce":1
                }
            },
            "txHash": "0x5ad20e534dea3f56f0aa84f55e364a2a9ac8b9b36ba0ff93c74fd98859955d21"
        })";

        EXPECT_EQ(
            nlohmann::json::parse(expected),
            nlohmann::json::from_cbor(encoded_pre_state_trace));
    }

    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, access_list_trace)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto sender =
        0x00000000000000000000000000000000deadbeef_address;

    // SSTORE(1, 1)
    static constexpr auto contract_address =
        0x00000000000000000000000000000000aaaaaaaa_address;
    auto const contract_code = 0x6001600155_bytes;
    auto const contract_code_hash = to_bytes(keccak256(contract_code));
    auto const contract_icode = monad::vm::make_shared_intercode(contract_code);

    auto const header = BlockHeader{.number = 256};

    commit_sequential(
        tdb,
        StateDeltas{
            {sender,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = NULL_HASH}}}},
            {contract_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0, .code_hash = contract_code_hash}}}}},
        Code{
            {contract_code_hash, contract_icode},
        },
        header);

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 1'000'000,
        .value = 0,
        .to = contract_address,
    };

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(sender)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;

    {
        boost::fibers::future<void> f = ctx.promise.get_future();
        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)&ctx,
            ACCESS_LIST_TRACER,
            true);
        f.get();

        ASSERT_TRUE(ctx.result->status_code == EVMC_SUCCESS);

        std::vector<uint8_t> const encoded_trace(
            ctx.result->encoded_trace,
            ctx.result->encoded_trace + ctx.result->encoded_trace_len);

        auto const *const expected = R"([
            {
                "address" : "0x00000000000000000000000000000000aaaaaaaa",
                "storageKeys" : [
                    "0x0000000000000000000000000000000000000000000000000000000000000001"
                ]
            }
        ])";

        EXPECT_EQ(
            nlohmann::json::parse(expected),
            nlohmann::json::from_cbor(encoded_trace));
    }

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, access_list_trace_empty)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto sender =
        0x00000000000000000000000000000000deadbeef_address;

    // STOP
    static constexpr auto contract_address =
        0x00000000000000000000000000000000aaaaaaaa_address;
    auto const contract_code = 0x00_bytes;
    auto const contract_code_hash = to_bytes(keccak256(contract_code));
    auto const contract_icode = monad::vm::make_shared_intercode(contract_code);

    auto const header = BlockHeader{.number = 256};

    commit_sequential(
        tdb,
        StateDeltas{
            {sender,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = NULL_HASH}}}},
            {contract_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0, .code_hash = contract_code_hash}}}}},
        Code{
            {contract_code_hash, contract_icode},
        },
        header);

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 1'000'000,
        .value = 0,
        .to = contract_address,
    };

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(sender)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;

    {
        boost::fibers::future<void> f = ctx.promise.get_future();
        monad_executor_eth_call_submit(
            executor,
            CHAIN_CONFIG_MONAD_DEVNET,
            rlp_tx.data(),
            rlp_tx.size(),
            rlp_header.data(),
            rlp_header.size(),
            rlp_sender.data(),
            rlp_sender.size(),
            header.number,
            rlp_block_id.data(),
            rlp_block_id.size(),
            state_override,
            complete_callback,
            (void *)&ctx,
            ACCESS_LIST_TRACER,
            true);
        f.get();

        ASSERT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
        EXPECT_EQ(ctx.result->encoded_trace, nullptr);
        EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    }

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}

TEST_F(EthCallFixture, access_list_trace_nested)
{
    static constexpr auto sender =
        0x00000000000000000000000000000000deadbeef_address;

    // SSTORE(0, 2); CALL(b)
    static constexpr auto a_address =
        0x00000000000000000000000000000000aaaaaaaa_address;
    auto const a_code =
        0x60025f555f5f5f5f5f7300000000000000000000000000000000bbbbbbbb5af1_bytes;
    auto const a_code_hash = to_bytes(keccak256(a_code));
    auto const a_icode = monad::vm::make_shared_intercode(a_code);

    // SSTORE(1, 1)
    static constexpr auto b_address =
        0x00000000000000000000000000000000bbbbbbbb_address;
    auto const b_code = 0x6001600155_bytes;
    auto const b_code_hash = to_bytes(keccak256(b_code));
    auto const b_icode = monad::vm::make_shared_intercode(b_code);

    commit_sequential(
        tdb,
        StateDeltas{
            {sender,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = NULL_HASH}}}},
            {a_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = a_code_hash}}}},
            {b_address,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = b_code_hash}}}}},
        Code{
            {a_code_hash, a_icode},
            {b_code_hash, b_icode},
        },
        BlockHeader{.number = 0});
    BlockHeader const header{.number = 0};

    Transaction const tx{
        .max_fee_per_gas = 1,
        .gas_limit = 1'000'000,
        .value = 0,
        .to = a_address,
        .data = byte_string{},
    };

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(sender)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto *executor = create_executor(dbname.string());
    auto *state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();

    monad_executor_eth_call_submit(
        executor,
        CHAIN_CONFIG_MONAD_DEVNET,
        rlp_tx.data(),
        rlp_tx.size(),
        rlp_header.data(),
        rlp_header.size(),
        rlp_sender.data(),
        rlp_sender.size(),
        header.number,
        rlp_block_id.data(),
        rlp_block_id.size(),
        state_override,
        complete_callback,
        (void *)&ctx,
        ACCESS_LIST_TRACER,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);

    std::vector<uint8_t> const encoded_trace(
        ctx.result->encoded_trace,
        ctx.result->encoded_trace + ctx.result->encoded_trace_len);

    auto const *const expected = R"([
        {
            "address" : "0x00000000000000000000000000000000aaaaaaaa",
            "storageKeys" : [
                "0x0000000000000000000000000000000000000000000000000000000000000000"
            ]
        },
        {
            "address" : "0x00000000000000000000000000000000bbbbbbbb",
            "storageKeys" : [
                "0x0000000000000000000000000000000000000000000000000000000000000001"
            ]
        }
    ])";

    EXPECT_EQ(
        nlohmann::json::parse(expected),
        nlohmann::json::from_cbor(encoded_trace));

    monad_state_override_destroy(state_override);
    monad_executor_destroy(executor);
}
