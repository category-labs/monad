#include <monad/chain/chain_config.h>
#include <monad/core/block.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/trace/rlp/call_frame_rlp.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/rpc/eth_call.h>
#include <test_resource_data.h>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <deque>
#include <memory>
#include <ranges>
#include <vector>

using namespace monad;
using namespace monad::test;

namespace
{
    constexpr unsigned node_lru_size = 10240;

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

        auto executor = monad_eth_call_executor_create(
            1, 1, node_lru_size, 30, dbname.string().c_str());
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
            mpt::INVALID_ROUND_NUM,
            state_override,
            complete_callback,
            (void *)&ctx,
            true,
            gas_specified);
        f.get();

        EXPECT_EQ(ctx.result->status_code, EVMC_SUCCESS);

        byte_string const rlp_call_frames(
            ctx.result->rlp_call_frames, ctx.result->rlp_call_frames_len);
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

    auto executor = monad_eth_call_executor_create(
        1, 1, node_lru_size, 30, dbname.string().c_str());
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
        mpt::INVALID_ROUND_NUM,
        state_override,
        complete_callback,
        (void *)&ctx,
        false,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
    EXPECT_TRUE(ctx.result->rlp_call_frames_len == 0);
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

    auto executor = monad_eth_call_executor_create(
        1, 1, node_lru_size, 30, dbname.string().c_str());
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
        mpt::INVALID_ROUND_NUM,
        state_override,
        complete_callback,
        (void *)&ctx,
        false,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_REJECTED);
    EXPECT_TRUE(std::strcmp(ctx.result->message, "insufficient balance") == 0);
    EXPECT_TRUE(ctx.result->rlp_call_frames_len == 0);
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

    auto const consensus_header =
        MonadConsensusBlockHeader::from_eth_header(header);
    tdb.commit({}, {}, consensus_header);
    tdb.set_block_and_round(header.number, consensus_header.round);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));

    auto executor = monad_eth_call_executor_create(
        1, 1, node_lru_size, 30, dbname.string().c_str());
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
        consensus_header.round,
        state_override,
        complete_callback,
        (void *)&ctx,
        false,
        true);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_SUCCESS);
    EXPECT_EQ(ctx.result->rlp_call_frames_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 21000);

    monad_state_override_destroy(state_override);
    monad_eth_call_executor_destroy(executor);
}

TEST_F(EthCallFixture, failed_to_read)
{
    // missing 256 previous blocks
    load_header(db, BlockHeader{.number = 1199});
    tdb.set_block_and_round(1199);
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

    auto executor = monad_eth_call_executor_create(
        1, 1, node_lru_size, 30, dbname.string().c_str());
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
        mpt::INVALID_ROUND_NUM,
        state_override,
        complete_callback,
        (void *)&ctx,
        false,
        true);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_REJECTED);
    EXPECT_TRUE(
        std::strcmp(
            ctx.result->message, "failure to initialize block hash buffer") ==
        0);
    EXPECT_EQ(ctx.result->rlp_call_frames_len, 0);
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

    Transaction tx{.gas_limit = 100000u, .data = from_hex(tx_data)};
    BlockHeader header{.number = 256};

    commit_sequential(tdb, {}, {}, header);

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender =
        to_vec(rlp::encode_address(std::make_optional(from)));

    auto executor = monad_eth_call_executor_create(
        1, 1, node_lru_size, 30, dbname.string().c_str());
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
        mpt::INVALID_ROUND_NUM,
        state_override,
        complete_callback,
        (void *)&ctx,
        false,
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
    EXPECT_EQ(ctx.result->rlp_call_frames_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 68137);

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

    auto executor = monad_eth_call_executor_create(
        1, 1, node_lru_size, 30, dbname.string().c_str());
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
        mpt::INVALID_ROUND_NUM,
        state_override,
        complete_callback,
        (void *)&ctx,
        false,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
    EXPECT_EQ(ctx.result->output_data_len, 0);
    EXPECT_EQ(ctx.result->rlp_call_frames_len, 0);
    EXPECT_EQ(ctx.result->gas_refund, 0);
    EXPECT_EQ(ctx.result->gas_used, 32094);

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

    auto executor = monad_eth_call_executor_create(
        2, 10, node_lru_size, 30, dbname.string().c_str());

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
            mpt::INVALID_ROUND_NUM,
            state_override,
            complete_callback,
            (void *)ctx.get(),
            false,
            true);
    }

    for (auto [ctx, f, state_override] :
         std::views::zip(ctxs, futures, state_overrides)) {
        f.get();

        EXPECT_TRUE(ctx->result->status_code == EVMC_SUCCESS);
        EXPECT_EQ(ctx->result->output_data_len, 0);
        EXPECT_EQ(ctx->result->rlp_call_frames_len, 0);
        EXPECT_EQ(ctx->result->gas_refund, 0);
        EXPECT_EQ(ctx->result->gas_used, 32094);

        monad_state_override_destroy(state_override);
    }

    monad_eth_call_executor_destroy(executor);
}

TEST_F(EthCallFixture, transfer_success_with_trace)
{
    test_transfer_call_with_trace(true);
}

TEST_F(EthCallFixture, transfer_success_with_trace_unspecified_gas)
{
    test_transfer_call_with_trace(false);
}

TEST_F(EthCallFixture, static_precompile_OOG_with_trace)
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

    auto executor = monad_eth_call_executor_create(
        1, 1, node_lru_size, 30, dbname.string().c_str());
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
        mpt::INVALID_ROUND_NUM,
        state_override,
        complete_callback,
        (void *)&ctx,
        true,
        true);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_OUT_OF_GAS);

    byte_string const rlp_call_frames(
        ctx.result->rlp_call_frames, ctx.result->rlp_call_frames_len);

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
