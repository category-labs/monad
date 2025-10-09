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

#include <category/core/bytes.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/rpc/eth_call.h>
#include <test_resource_data.h>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <deque>
#include <memory>
#include <ranges>
#include <vector>

using namespace monad;
using namespace monad::test;
using namespace monad::trace;

namespace
{
    constexpr uint64_t node_lru_max_mem =
        10240 * mpt::NodeCache::AVERAGE_NODE_SIZE;
    constexpr unsigned max_timeout = std::numeric_limits<unsigned>::max();
    auto const rlp_finalized_id = rlp::encode_bytes32(bytes32_t{});

    auto create_executor(std::string const &dbname)
    {
        monad_eth_call_pool_config conf = {1, 1, max_timeout, 1000};
        return monad_eth_call_executor_create(
            conf, conf, node_lru_max_mem, dbname.c_str());
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
        monad_eth_call_result *result;
        boost::fibers::promise<void> promise;

        ~callback_context()
        {
            monad_eth_call_result_release(result);
        }
    };

    void complete_callback(monad_eth_call_result *result, void *user)
    {
        auto c = (callback_context *)user;

        c->result = result;
        c->promise.set_value();
    }

    void EthCallFixture::test_transfer_call_with_trace(bool const gas_specified)
    {
        for (uint64_t i = 0; i < 256; ++i) {
            commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
        }

        BlockHeader header{.number = 256};

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

        auto executor = create_executor(dbname.string());
        auto state_override = monad_state_override_create();

        struct callback_context ctx;
        boost::fibers::future<void> f = ctx.promise.get_future();

        monad_eth_call_executor_submit(
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
        CallFrame expected{
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
        monad_eth_call_executor_destroy(executor);
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

    Transaction tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
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

    Transaction tx{
        .gas_limit = 100000u,
        .value = 1000000000000,
        .to = to,
        .type = TransactionType::eip1559};
    BlockHeader header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
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

    Transaction tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader header{.number = 256};

    tdb.commit({}, {}, bytes32_t{256}, header);
    tdb.set_block_and_prefix(header.number, bytes32_t{256});

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp::encode_bytes32(bytes32_t{256}));

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
}

TEST_F(EthCallFixture, failed_to_read)
{
    // missing 256 previous blocks
    load_header(db, BlockHeader{.number = 1199});
    tdb.set_block_and_prefix(1199);
    for (uint64_t i = 1200; i < 1256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto to{
        0x5353535353535353535353535353535353535353_address};

    Transaction tx{
        .gas_limit = 100000u, .to = to, .type = TransactionType::eip1559};
    BlockHeader header{.number = 1256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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

    EXPECT_EQ(ctx.result->status_code, EVMC_REJECTED);
    EXPECT_TRUE(
        std::strcmp(
            ctx.result->message, "failure to initialize block hash buffer") ==
        0);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 0);

    monad_state_override_destroy(state_override);
    monad_eth_call_executor_destroy(executor);
}

TEST_F(EthCallFixture, contract_deployment_success)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from = Address{};

    std::string tx_data =
        "0x604580600e600039806000f350fe7fffffffffffffffffffffffffffffffffffffff"
        "ffffffffffffffffffffffffe03601600081602082378035828234f580151560395781"
        "82fd5b8082525050506014600cf3";

    Transaction tx{.gas_limit = 200000u, .data = from_hex(tx_data)};
    BlockHeader header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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

    std::string deployed_code =
        "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe036"
        "01600081602082378035828234f58015156039578182fd5b8082525050506014600cf"
        "3";
    byte_string deployed_code_bytes = from_hex(deployed_code);

    std::vector<uint8_t> deployed_code_vec = {
        deployed_code_bytes.data(),
        deployed_code_bytes.data() + deployed_code_bytes.size()};

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);

    std::vector<uint8_t> returned_code_vec(
        ctx.result->output_data,
        ctx.result->output_data + ctx.result->output_data_len);
    EXPECT_EQ(returned_code_vec, deployed_code_vec);
    EXPECT_EQ(ctx.result->encoded_trace_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 137'137);

    monad_state_override_destroy(state_override);
    monad_eth_call_executor_destroy(executor);
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

    Transaction tx{
        .gas_limit = 21'000u,
        .value = 1,
        .to = to,
        .data = {},
    };

    BlockHeader header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
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
    auto const code2 = evmc::from_hex("0x59595959600260FF5AF1").value();
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

    Transaction tx{
        .gas_limit = 1'000'000u,
        .value = 1,
        .to = addr2,
        .type = TransactionType::eip1559,
    };

    BlockHeader header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(addr1)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
}

TEST_F(EthCallFixture, loop_out_of_gas)
{
    auto const code = evmc::from_hex("0x5B5F56").value();
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

    Transaction tx{.gas_limit = 100000u, .to = ca, .data = {}};

    BlockHeader header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender = to_vec(rlp::encode_address(std::make_optional(ca)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
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
        evmc::from_hex("0x56cde25b000000000000000000000000000000000000000000000"
                       "0000000000000000000000000000000000000000000000000000000"
                       "0000000000000000000000004e20")
            .value();
    Transaction tx{.gas_limit = 30'000'000u, .to = ca, .data = data};

    BlockHeader header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender = to_vec(rlp::encode_address(std::make_optional(ca)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
}

TEST_F(EthCallFixture, from_contract_account)
{
    using namespace intx;

    auto const code =
        evmc::from_hex("0x6000600155600060025560006003556000600455600060055500")
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

    std::string tx_data = "0x60025560";

    Transaction tx{.gas_limit = 100000u, .to = ca, .data = from_hex(tx_data)};

    BlockHeader header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender = to_vec(rlp::encode_address(std::make_optional(ca)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();
    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
}

TEST_F(EthCallFixture, concurrent_eth_calls)
{
    using namespace intx;

    auto const ca = 0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    for (uint64_t i = 0; i < 300; ++i) {
        if (i == 200) {
            auto const code =
                evmc::from_hex(
                    "0x6000600155600060025560006003556000600455600060055500")
                    .value();
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

    std::string tx_data = "0x60025560";

    Transaction tx{.gas_limit = 100000u, .to = ca, .data = from_hex(tx_data)};

    auto executor = create_executor(dbname.string());

    std::deque<std::unique_ptr<callback_context>> ctxs;
    std::deque<boost::fibers::future<void>> futures;
    std::deque<monad_state_override *> state_overrides;

    for (uint64_t b = 200; b < 300; ++b) {
        auto &ctx = ctxs.emplace_back(std::make_unique<callback_context>());
        futures.emplace_back(ctx->promise.get_future());
        auto *const state_override =
            state_overrides.emplace_back(monad_state_override_create());

        BlockHeader header{.number = b};

        auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
        auto const rlp_header = to_vec(rlp::encode_block_header(header));
        auto const rlp_sender =
            to_vec(rlp::encode_address(std::make_optional(ca)));
        auto const rlp_block_id = to_vec(rlp_finalized_id);

        monad_eth_call_executor_submit(
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

    monad_eth_call_executor_destroy(executor);
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
        evmc::from_hex("600160025f5fa25f5f5f5f5f7300000000000000000000000000000"
                       "000bbbbbbbb5af115604d575f5f5f5f5f7300000000000000000000"
                       "000000000000cccccccc5af115604d5760035f5fa1005bfe")
            .value();
    auto const a_code_hash = to_bytes(keccak256(a_code));
    auto const a_icode = monad::vm::make_shared_intercode(a_code);

    // CALL(d_address)
    static constexpr auto b_address =
        0x00000000000000000000000000000000bbbbbbbb_address;
    auto const b_code =
        evmc::from_hex(
            "0x5f5f5f5f5f7300000000000000000000000000000000dddddddd5af1")
            .value();
    auto const b_code_hash = to_bytes(keccak256(b_code));
    auto const b_icode = monad::vm::make_shared_intercode(b_code);

    // MSTORE(0, 0xFF...FE); LOG1(1, 0, 32)
    static constexpr auto c_address =
        0x00000000000000000000000000000000cccccccc_address;
    auto const c_code = evmc::from_hex("0x60025f035f52600160205fa1").value();
    auto const c_code_hash = to_bytes(keccak256(c_code));
    auto const c_icode = monad::vm::make_shared_intercode(c_code);

    // STOP
    static constexpr auto d_address =
        0x00000000000000000000000000000000dddddddd_address;
    auto const d_code = evmc::from_hex("0x00").value();
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
    BlockHeader header{.number = 0};

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

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();

    monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
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

    BlockHeader header{.number = 256};

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

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context ctx;
    boost::fibers::future<void> f = ctx.promise.get_future();

    monad_eth_call_executor_submit(
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

    CallFrame expected{
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
    monad_eth_call_executor_destroy(executor);
}

// Same setup as transfer_success_with_call_trace, include both prestate &
// statedelta trace checks
TEST_F(EthCallFixture, transfer_success_with_state_trace)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    BlockHeader header{.number = 256};

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

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    struct callback_context prestate_ctx;
    struct callback_context statediff_ctx;

    // PreState
    {
        boost::fibers::future<void> f = prestate_ctx.promise.get_future();

        monad_eth_call_executor_submit(
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
            OriginalAccountState as_from{acct_from};
            expected.emplace(ADDR_A, as_from);

            OriginalAccountState as_to{acct_to};
            expected.emplace(ADDR_B, as_to);

            OriginalAccountState as_bene{std::nullopt};
            expected.emplace(header.beneficiary, as_bene);
        }

        EXPECT_EQ(
            state_to_json(expected, s),
            nlohmann::json::from_cbor(encoded_pre_state_trace));
    }

    // StateDelta
    {
        boost::fibers::future<void> f = statediff_ctx.promise.get_future();

        monad_eth_call_executor_submit(
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
    monad_eth_call_executor_destroy(executor);
}

// same setup as contract_deployment_success, but with prestate and statediff
// tracer
TEST_F(EthCallFixture, contract_deployment_success_with_state_trace)
{
    for (uint64_t i = 0; i < 256; ++i) {
        commit_sequential(tdb, {}, {}, BlockHeader{.number = i});
    }

    static constexpr auto from = Address{};

    std::string tx_data =
        "0x604580600e600039806000f350fe7fffffffffffffffffffffffffffffffffffffff"
        "ffffffffffffffffffffffffe03601600081602082378035828234f580151560395781"
        "82fd5b8082525050506014600cf3";

    Transaction tx{.gas_limit = 200000u, .data = from_hex(tx_data)};
    BlockHeader header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));
    auto const rlp_block_id = to_vec(rlp_finalized_id);

    auto executor = create_executor(dbname.string());
    auto state_override = monad_state_override_create();

    std::string deployed_code =
        "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe036"
        "01600081602082378035828234f58015156039578182fd5b8082525050506014600cf"
        "3";
    byte_string deployed_code_bytes = from_hex(deployed_code);

    std::vector<uint8_t> deployed_code_vec = {
        deployed_code_bytes.data(),
        deployed_code_bytes.data() + deployed_code_bytes.size()};

    struct callback_context prestate_ctx;
    struct callback_context statediff_ctx;

    // PreState trace
    {
        boost::fibers::future<void> f = prestate_ctx.promise.get_future();
        monad_eth_call_executor_submit(
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

        auto const expected = R"({
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
        monad_eth_call_executor_submit(
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

        auto const expected = R"({
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
    monad_eth_call_executor_destroy(executor);
}
