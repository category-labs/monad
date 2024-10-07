#include <monad/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>
#include <test_resource_data.h>

#include <ethash/keccak.hpp>
#include <gtest/gtest.h>

#include <deque>
#include <filesystem>
#include <fstream>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

struct monad_statesync_client
{
    std::deque<monad_sync_request> rqs;
};

struct monad_statesync_server_network
{
    monad_statesync_client *client;
    monad_statesync_client_context *cctx;
    byte_string buf;
};

namespace
{
    auto const genesis = test_resource::ethereum_genesis_dir / "mainnet.json";

    std::filesystem::path tmp_dbname()
    {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_statesync_test_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        char const *const path = dbname.c_str();
        OnDiskMachine machine;
        mpt::Db const db{
            machine,
            mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
        return dbname;
    }

    void statesync_send_request(
        monad_statesync_client *const client, monad_sync_request const rq)
    {
        client->rqs.push_back(rq);
    }

    monad_sync_target make_target(uint64_t const n, bytes32_t const root)
    {
        monad_sync_target target;
        target.n = n;
        std::memcpy(target.state_root, root.bytes, sizeof(root.bytes));
        return target;
    }

    ssize_t statesync_server_recv(
        monad_statesync_server_network *const net, unsigned char *const buf,
        size_t const len)
    {
        if (len == 1) {
            constexpr auto MSG_TYPE = SyncTypeRequest;
            std::memcpy(buf, &MSG_TYPE, 1);
        }
        else {
            EXPECT_EQ(len, sizeof(monad_sync_request));
            std::memcpy(
                buf, &net->client->rqs.front(), sizeof(monad_sync_request));
            net->client->rqs.pop_front();
        }
        return static_cast<ssize_t>(len);
    }

    void statesync_server_send_upsert(
        monad_statesync_server_network *const net, monad_sync_type const type,
        unsigned char const *const v1, uint64_t const size1,
        unsigned char const *const v2, uint64_t const size2)
    {
        net->buf.clear();
        if (v1 != nullptr) {
            net->buf.append(v1, size1);
        }
        if (v2 != nullptr) {
            net->buf.append(v2, size2);
        }
        monad_statesync_client_handle_upsert(
            net->cctx, type, net->buf.data(), net->buf.size());
    }

    void statesync_server_send_done(
        monad_statesync_server_network *const net, monad_sync_done const done)
    {
        monad_statesync_client_handle_done(net->cctx, done);
    }

    struct StateSyncFixture : public ::testing::Test
    {
        std::filesystem::path cdbname;
        monad_statesync_client client;
        monad_statesync_client_context *cctx;
        std::filesystem::path sdbname;
        OnDiskMachine machine;
        mpt::Db sdb;
        TrieDb stdb;
        monad_statesync_server_context sctx;
        mpt::Db ro;
        monad_statesync_server_network net;
        monad_statesync_server *server{};

        StateSyncFixture()
            : cdbname{tmp_dbname()}
            , cctx{nullptr}
            , sdbname{tmp_dbname()}
            , sdb{machine,
                  OnDiskDbConfig{.append = true, .dbname_paths = {sdbname}}}
            , stdb{sdb}
            , sctx{stdb}
            , ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {sdbname}}}
        {
            sctx.ro = &ro;
        }

        void init()
        {
            char const *const str = cdbname.c_str();
            cctx = monad_statesync_client_context_create(
                &str, 1, genesis.c_str(), &client, &statesync_send_request);
            net = {.client = &client, .cctx = cctx};
            server = monad_statesync_server_create(
                &sctx,
                &net,
                &statesync_server_recv,
                &statesync_server_send_upsert,
                &statesync_server_send_done);
        }

        void run()
        {
            while (!client.rqs.empty()) {
                monad_statesync_server_run_once(server);
            }
            EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
        }

        ~StateSyncFixture()
        {
            monad_statesync_client_context_destroy(cctx);
            monad_statesync_server_destroy(server);
            std::filesystem::remove(cdbname);
            std::filesystem::remove(sdbname);
        }
    };
}

TEST_F(StateSyncFixture, genesis)
{
    init();
    monad_statesync_client_handle_target(
        cctx,
        make_target(
            0,
            0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544_bytes32));
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_from_latest)
{
    {
        OnDiskMachine machine;
        mpt::Db db{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb tdb{db};
        load_db(tdb, 1'000'000);
        init();
    }
    monad_statesync_client_handle_target(
        cctx,
        make_target(
            1'000'000,
            0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32));
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_from_empty)
{
    {
        load_db(stdb, 1'000'000);
        init();
    }
    monad_statesync_client_handle_target(
        cctx,
        make_target(
            1'000'000,
            0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32));
    run();
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));

    OnDiskMachine machine;
    mpt::Db cdb{
        machine,
        mpt::OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
    TrieDb ctdb{cdb};
    EXPECT_EQ(ctdb.get_block_number(), 1'000'000);
    EXPECT_TRUE(ctdb.read_account(ADDR_A).has_value());
    EXPECT_EQ(ctdb.read_code(A_CODE_HASH)->executable_code, A_CODE);
    EXPECT_EQ(ctdb.read_code(B_CODE_HASH)->executable_code, B_CODE);
    EXPECT_EQ(ctdb.read_code(C_CODE_HASH)->executable_code, C_CODE);
    EXPECT_EQ(ctdb.read_code(D_CODE_HASH)->executable_code, D_CODE);
    EXPECT_EQ(ctdb.read_code(E_CODE_HASH)->executable_code, E_CODE);
    EXPECT_EQ(ctdb.read_code(H_CODE_HASH)->executable_code, H_CODE);
}

TEST_F(StateSyncFixture, sync_from_some)
{
    {
        OnDiskMachine machine;
        mpt::Db db{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb tdb{db};
        read_genesis(genesis, tdb);
        read_genesis(genesis, stdb);
        init();
    }

    // delete existing account
    {
        constexpr auto ADDR1 =
            0x000d836201318ec6899a67540690382780743280_address;
        auto const acct = stdb.read_account(ADDR1);
        MONAD_ASSERT(acct.has_value());
        stdb.increment_block_number();
        sctx.commit(
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            {});
    }
    // new storage to existing account
    {
        constexpr auto ADDR1 =
            0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
        auto const acct = stdb.read_account(ADDR1);
        stdb.increment_block_number();
        sctx.commit(
            StateDeltas{
                {ADDR1,
                 {.account = {acct, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
            Code{},
            {});
    }
    // add new smart contract
    {
        constexpr auto ADDR1 =
            0x5353535353535353535353535353535353535353_address;
        stdb.increment_block_number();

        auto const code =
            evmc::from_hex(
                "7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                "ffffffffffffffffffffff0160005500")
                .value();
        auto const code_hash = to_bytes(keccak256(code));
        auto const code_analysis =
            std::make_shared<CodeAnalysis>(analyze(code));

        sctx.commit(
            StateDeltas{
                {ADDR1,
                 {.account =
                      {std::nullopt,
                       Account{
                           .balance = 1337,
                           .code_hash = code_hash,
                           .nonce = 1,
                           .incarnation = Incarnation{3, 0}}},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}

            },
            Code{{code_hash, code_analysis}},
            {});
    }
    // delete storage
    {
        constexpr auto ADDR1 =
            0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
        auto const acct = stdb.read_account(ADDR1);
        stdb.increment_block_number();
        sctx.commit(
            StateDeltas{
                {ADDR1,
                 {.account = {acct, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {0x0000000000000013370000000000000000000000000000000000000000000003_bytes32,
                         {}}}}}}},
            Code{},
            {});
    }
    // account incarnation
    {
        constexpr auto ADDR1 =
            0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
        auto const old = stdb.read_account(ADDR1);
        auto acct = old;
        acct->incarnation = Incarnation{5, 0};
        stdb.increment_block_number();
        sctx.commit(
            StateDeltas{
                {ADDR1,
                 {.account = {old, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
            Code{},
            {});
    }
    // delete smart contract
    {
        constexpr auto ADDR1 =
            0x5353535353535353535353535353535353535353_address;
        auto const acct = stdb.read_account(ADDR1);
        MONAD_ASSERT(acct.has_value());
        stdb.increment_block_number();
        sctx.commit(
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            {});
    }

    auto const ctmp = tmp_dbname();
    auto const cdbname = ctmp.c_str();
    {
        OnDiskMachine machine;
        mpt::Db cdb{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb ctdb{cdb};
        read_genesis(genesis, ctdb);
    }

    monad_statesync_client_handle_target(
        cctx,
        make_target(
            1,
            0x5d651a344741e37c613b580048934ae0deb58b72b542b61416cf7d1fb81d5a79_bytes32));
    run();

    monad_statesync_client_handle_target(
        cctx,
        make_target(
            2,
            0xd1afa4d8e4546cd3ca0314f2ea5ed7c2de22162b2d72b0ca3f56bcfa551e9e5f_bytes32));
    run();

    monad_statesync_client_handle_target(
        cctx,
        make_target(
            3,
            0x1922e617443693307d169df71f44688795793a91c4bf40742765c096e00413d7_bytes32));
    run();

    monad_statesync_client_handle_target(
        cctx,
        make_target(
            4,
            0x589b5012c41144a33447c07b0cc1f3108181774b7f1eec1fa0f466ffa9bc74b3_bytes32));
    run();

    monad_statesync_client_handle_target(
        cctx,
        make_target(
            5,
            0x1922e617443693307d169df71f44688795793a91c4bf40742765c096e00413d7_bytes32));
    run();

    monad_statesync_client_handle_target(
        cctx,
        make_target(
            6,
            0xd1afa4d8e4546cd3ca0314f2ea5ed7c2de22162b2d72b0ca3f56bcfa551e9e5f_bytes32));
    run();

    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, ignore_unused_code)
{
    {
        load_db(stdb, 1'000'000);
        init();
    }

    auto const code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                       "ffffffffffffffffffffffff")
            .value();
    auto const code_hash = to_bytes(keccak256(code));
    monad_statesync_client_handle_target(
        cctx,
        make_target(
            1'000'000,
            0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32));
    // send some random code
    statesync_server_send_upsert(
        &net, SyncTypeUpsertCode, code.data(), code.size(), nullptr, 0);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
    OnDiskMachine machine;
    mpt::Db cdb{
        machine,
        mpt::OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
    TrieDb ctdb{cdb};
    EXPECT_TRUE(ctdb.read_code(code_hash)->executable_code.empty());
}

TEST_F(StateSyncFixture, sync_one_account)
{
    stdb.set_block_number(1'000'000);
    stdb.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage = {}}}},
        Code{});
    auto const expected_root = stdb.state_root();
    init();
    monad_statesync_client_handle_target(
        cctx, make_target(1'000'000, expected_root));
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_empty)
{
    stdb.set_block_number(1'000'000);
    stdb.commit(StateDeltas{}, Code{});
    init();
    monad_statesync_client_handle_target(
        cctx, make_target(1'000'000, NULL_ROOT));
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, account_updated_after_storage)
{
    stdb.set_block_number(100);
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage =
                     {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                       {bytes32_t{},
                        0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
        Code{},
        {});
    stdb.increment_block_number();
    sctx.commit({}, {}, {});
    stdb.increment_block_number();
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, Account{.balance = 200}},
                 .storage = {}}}},
        {},
        {});
    init();
    monad_statesync_client_handle_target(
        cctx, make_target(102, stdb.state_root()));
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, account_deleted_after_storage)
{
    stdb.set_block_number(100);
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage =
                     {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                       {bytes32_t{},
                        0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
        Code{},
        {});
    stdb.increment_block_number();
    sctx.commit({}, {}, {});
    stdb.increment_block_number();
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, std::nullopt},
                 .storage = {}}}},
        {},
        {});
    init();
    monad_statesync_client_handle_target(cctx, make_target(102, NULL_ROOT));
}

TEST_F(StateSyncFixture, account_deleted_and_prefix_skipped)
{
    init();
    stdb.increment_block_number();
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage = {}}}},
        {},
        {});
    monad_statesync_client_handle_target(
        cctx, make_target(1, sctx.state_root()));
    run();

    stdb.increment_block_number();
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, std::nullopt},
                 .storage = {}}}},
        {},
        {});
    monad_statesync_client_handle_target(
        cctx, make_target(2, sctx.state_root()));
    client.rqs.clear();

    stdb.increment_block_number();
    sctx.commit({}, {}, {});
    monad_statesync_client_handle_target(
        cctx, make_target(3, sctx.state_root()));
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, benchmark)
{
    constexpr auto N = 1'000'000;
    std::vector<std::pair<Address, StateDelta>> v;
    v.reserve(N);
    for (uint64_t i = 0; i < N; ++i) {
        v.emplace_back(
            i,
            StateDelta{
                .account = {std::nullopt, Account{.balance = i, .nonce = i}},
                .storage = {}});
    }
    stdb.set_block_number(1'000'000);
    StateDeltas deltas{v.begin(), v.end()};
    stdb.commit(deltas, Code{});
    auto const expected_root = stdb.state_root();
    init();
    monad_statesync_client_handle_target(
        cctx, make_target(1'000'000, expected_root));
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}
