#include <monad/chain/chain_config.h>
#include <monad/core/block.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/rpc/eth_call.h>
#include <test_resource_data.h>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <vector>

using namespace monad;
using namespace monad::test;

namespace
{
    std::vector<uint8_t> to_vec(byte_string const &bs)
    {
        std::vector<uint8_t> v{bs.begin(), bs.end()};
        return v;
    }

    // TODO: consolidate fixtures
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
    };

    struct callback_context {
        monad_eth_call_result *result;
        boost::fibers::promise<void> promise;

        ~callback_context()
        {
            monad_eth_call_result_release(result);
        }
    };

    void complete_callback(monad_eth_call_result * result, void * user)
    {
        auto c = (callback_context *)user;

        c->result = result;
        c->promise.set_value();
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

    auto executor = monad_eth_call_executor_create(1, dbname.string().c_str());
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
        (void*)&ctx);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
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

    auto executor = monad_eth_call_executor_create(1, dbname.string().c_str());
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
        (void*)&ctx);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_REJECTED);
    EXPECT_TRUE(std::strcmp(ctx.result->message, "insufficient balance") == 0);

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

    auto executor = monad_eth_call_executor_create(1, dbname.string().c_str());
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
        (void*)&ctx);
    f.get();
    
    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
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

    auto executor = monad_eth_call_executor_create(1, dbname.string().c_str());
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
        (void*)&ctx);
    f.get();

    EXPECT_EQ(ctx.result->status_code, EVMC_REJECTED);
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

    auto executor = monad_eth_call_executor_create(1, dbname.string().c_str());
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
        (void*)&ctx);
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
    auto const code_analysis = std::make_shared<CodeAnalysis>(analyze(code));

    auto const ca = 0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    commit_sequential(
        tdb,
        StateDeltas{
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0x1b58, .code_hash = code_hash}}}}},
        Code{{code_hash, code_analysis}},
        BlockHeader{.number = 0});

    std::string tx_data = "0x60025560";

    Transaction tx{.gas_limit = 100000u, .to = ca, .data = from_hex(tx_data)};

    BlockHeader header{.number = 0};

    auto const rlp_tx = to_vec(rlp::encode_transaction(tx));
    auto const rlp_header = to_vec(rlp::encode_block_header(header));
    auto const rlp_sender = to_vec(rlp::encode_address(std::make_optional(ca)));

    auto executor = monad_eth_call_executor_create(1, dbname.string().c_str());
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
        (void*)&ctx);
    f.get();

    EXPECT_TRUE(ctx.result->status_code == EVMC_SUCCESS);
    EXPECT_EQ(ctx.result->output_data_len, 0);
    monad_state_override_destroy(state_override);
    monad_eth_call_executor_destroy(executor);
}
