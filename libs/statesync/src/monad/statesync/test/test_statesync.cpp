#include <monad/async/util.hpp>
#include <monad/core/assert.h>
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

struct monad_statesync_client
{
    std::deque<monad_sync_request> rqs;
};

struct monad_statesync_server_network
{
    monad_statesync_client *client;
    monad_statesync_client_context *cctx;
};

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

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
        monad_statesync_server_network *const net,
        unsigned char const *const key, uint64_t const key_size,
        unsigned char const *const value, uint64_t const value_size,
        bool const code)
    {
        monad_statesync_client_handle_upsert(
            net->cctx, key, key_size, value, value_size, code);
    }

    void statesync_server_send_done(
        monad_statesync_server_network *const net, monad_sync_done const done)
    {
        monad_statesync_client_handle_done(net->cctx, done);
    }
}

TEST(StateSync, genesis)
{
    auto const tmp = tmp_dbname();
    char const *const dbname = tmp.c_str();
    monad_statesync_client client;
    auto *const ctx = monad_statesync_client_context_create(
        &dbname, 1, genesis.c_str(), &client, &statesync_send_request);
    monad_statesync_client_handle_target(
        ctx,
        make_target(
            0,
            0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544_bytes32));
    EXPECT_TRUE(monad_statesync_client_has_reached_target(ctx));
    EXPECT_TRUE(monad_statesync_client_finalize(ctx));
    monad_statesync_client_context_destroy(ctx);
    std::filesystem::remove(tmp);
}

TEST(StateSync, sync_from_latest)
{
    auto const tmp = tmp_dbname();
    char const *const dbname = tmp.c_str();
    OnDiskMachine machine;
    mpt::Db db{
        machine, OnDiskDbConfig{.append = true, .dbname_paths = {dbname}}};
    std::ifstream accounts(test_resource::checkpoint_dir / "accounts");
    std::ifstream code(test_resource::checkpoint_dir / "code");
    load_from_binary(db, accounts, code, 1'000'000);
    monad_statesync_client client;
    auto *const ctx = monad_statesync_client_context_create(
        &dbname, 1, genesis.c_str(), &client, &statesync_send_request);
    monad_statesync_client_handle_target(
        ctx,
        make_target(
            1'000'000,
            0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32));
    EXPECT_TRUE(monad_statesync_client_has_reached_target(ctx));
    EXPECT_TRUE(monad_statesync_client_finalize(ctx));
    monad_statesync_client_context_destroy(ctx);
    std::filesystem::remove(tmp);
}

TEST(StateSync, sync_from_empty)
{
    auto const ctmp = tmp_dbname();
    auto const stmp = tmp_dbname();
    char const *const cdbname = ctmp.c_str();
    char const *const sdbname = stmp.c_str();

    monad_statesync_client client;
    auto *const cctx = monad_statesync_client_context_create(
        &cdbname, 1, genesis.c_str(), &client, &statesync_send_request);

    OnDiskMachine machine;
    mpt::Db db{
        machine, OnDiskDbConfig{.append = true, .dbname_paths = {sdbname}}};
    std::ifstream accounts(test_resource::checkpoint_dir / "accounts");
    std::ifstream code(test_resource::checkpoint_dir / "code");
    load_from_binary(db, accounts, code, 1'000'000);
    TrieDb tdb{db};
    monad_statesync_server_context sctx{tdb};
    mpt::Db ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {sdbname}}};
    sctx.ro = &ro;
    monad_statesync_server_network net{.client = &client, .cctx = cctx};
    auto *const server = monad_statesync_server_create(
        &sctx,
        &net,
        &statesync_server_recv,
        &statesync_server_send_upsert,
        &statesync_server_send_done);

    monad_statesync_client_handle_target(
        cctx,
        make_target(
            1'000'000,
            0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32));
    while (!client.rqs.empty()) {
        monad_statesync_server_run_once(server);
    }
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));

    monad_statesync_client_context_destroy(cctx);
    monad_statesync_server_destroy(server);
    std::filesystem::remove(ctmp);
    std::filesystem::remove(stmp);
}

TEST(StateSync, sync_from_some)
{
    auto const tmp = tmp_dbname();
    char const *const dbname = tmp.c_str();
    OnDiskMachine machine;
    mpt::Db db{
        machine, OnDiskDbConfig{.append = true, .dbname_paths = {dbname}}};
    TrieDb tdb{db};
    read_genesis(genesis, tdb);
    monad_statesync_server_context sctx{tdb};

    // delete existing account
    {
        constexpr auto ADDR1 =
            0x000d836201318ec6899a67540690382780743280_address;
        auto const acct = tdb.read_account(ADDR1);
        MONAD_ASSERT(acct.has_value());
        tdb.increment_block_number();
        sctx.commit(
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            {});
    }
    // new storage to existing account
    {
        constexpr auto ADDR1 =
            0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
        auto const acct = tdb.read_account(ADDR1);
        tdb.increment_block_number();
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
        tdb.increment_block_number();

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
        auto const acct = tdb.read_account(ADDR1);
        tdb.increment_block_number();
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
        auto const old = tdb.read_account(ADDR1);
        auto acct = old;
        acct->incarnation = Incarnation{5, 0};
        tdb.increment_block_number();
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
        auto const acct = tdb.read_account(ADDR1);
        MONAD_ASSERT(acct.has_value());
        tdb.increment_block_number();
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

    auto const sync = [&](uint64_t const n, bytes32_t const root) {
        monad_statesync_client client;
        auto *const cctx = monad_statesync_client_context_create(
            &cdbname, 1, genesis.c_str(), &client, &statesync_send_request);
        mpt::Db ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
        sctx.ro = &ro;
        monad_statesync_server_network net{.client = &client, .cctx = cctx};
        auto *const server = monad_statesync_server_create(
            &sctx,
            &net,
            &statesync_server_recv,
            &statesync_server_send_upsert,
            &statesync_server_send_done);
        monad_statesync_client_handle_target(cctx, make_target(n, root));
        while (!client.rqs.empty()) {
            monad_statesync_server_run_once(server);
        }
        EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
        EXPECT_TRUE(monad_statesync_client_finalize(cctx));
        monad_statesync_client_context_destroy(cctx);
        monad_statesync_server_destroy(server);
    };

    sync(
        1,
        0x5d651a344741e37c613b580048934ae0deb58b72b542b61416cf7d1fb81d5a79_bytes32);
    sync(
        2,
        0xd1afa4d8e4546cd3ca0314f2ea5ed7c2de22162b2d72b0ca3f56bcfa551e9e5f_bytes32);
    sync(
        3,
        0x1922e617443693307d169df71f44688795793a91c4bf40742765c096e00413d7_bytes32);
    sync(
        4,
        0x589b5012c41144a33447c07b0cc1f3108181774b7f1eec1fa0f466ffa9bc74b3_bytes32);
    sync(
        5,
        0x1922e617443693307d169df71f44688795793a91c4bf40742765c096e00413d7_bytes32);
    sync(
        6,
        0xd1afa4d8e4546cd3ca0314f2ea5ed7c2de22162b2d72b0ca3f56bcfa551e9e5f_bytes32);

    std::filesystem::remove(ctmp);
    std::filesystem::remove(tmp);
}

TEST(StateSync, ignore_unused_code)
{
    auto const tmp = tmp_dbname();
    auto const ctmp = tmp_dbname();
    char const *const cdbname = ctmp.c_str();
    auto const code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                       "ffffffffffffffffffffffff")
            .value();
    auto const code_hash = to_bytes(keccak256(code));
    {
        char const *const dbname = tmp.c_str();
        OnDiskMachine machine;
        mpt::Db db{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {dbname}}};
        {
            std::ifstream accounts(test_resource::checkpoint_dir / "accounts");
            std::ifstream code(test_resource::checkpoint_dir / "code");
            load_from_binary(db, accounts, code, 1'000'000);
        }
        TrieDb tdb{db};
        monad_statesync_server_context sctx{tdb};

        monad_statesync_client client;
        auto *const cctx = monad_statesync_client_context_create(
            &cdbname, 1, genesis.c_str(), &client, &statesync_send_request);
        mpt::Db ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
        sctx.ro = &ro;
        monad_statesync_server_network net{.client = &client, .cctx = cctx};
        auto *const server = monad_statesync_server_create(
            &sctx,
            &net,
            &statesync_server_recv,
            &statesync_server_send_upsert,
            &statesync_server_send_done);
        monad_statesync_client_handle_target(
            cctx,
            make_target(
                1'000'000,
                0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32));
        // send some random code
        statesync_server_send_upsert(
            &net,
            code_hash.bytes,
            sizeof(code_hash),
            code.data(),
            code.size(),
            true);
        while (!client.rqs.empty()) {
            monad_statesync_server_run_once(server);
        }
        EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
        EXPECT_TRUE(monad_statesync_client_finalize(cctx));
        monad_statesync_client_context_destroy(cctx);
        monad_statesync_server_destroy(server);
    }
    mpt::Db cdb{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {cdbname}}};
    TrieDb ctdb{cdb};
    EXPECT_TRUE(ctdb.read_code(code_hash)->executable_code.empty());

    std::filesystem::remove(ctmp);
    std::filesystem::remove(tmp);
}

TEST(StateSync, sync_one_account)
{
    auto const ctmp = tmp_dbname();
    auto const stmp = tmp_dbname();
    char const *const cdbname = ctmp.c_str();
    char const *const sdbname = stmp.c_str();

    monad_statesync_client client;
    auto *const cctx = monad_statesync_client_context_create(
        &cdbname, 1, genesis.c_str(), &client, &statesync_send_request);

    OnDiskMachine machine;
    mpt::Db db{
        machine, OnDiskDbConfig{.append = true, .dbname_paths = {sdbname}}};
    TrieDb tdb{db};
    tdb.set_block_number(1'000'000);
    tdb.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage = {}}}},
        Code{});
    auto const expected_root = tdb.state_root();
    monad_statesync_server_context sctx{tdb};
    mpt::Db ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {sdbname}}};
    sctx.ro = &ro;
    monad_statesync_server_network net{.client = &client, .cctx = cctx};
    auto *const server = monad_statesync_server_create(
        &sctx,
        &net,
        &statesync_server_recv,
        &statesync_server_send_upsert,
        &statesync_server_send_done);

    monad_statesync_client_handle_target(
        cctx, make_target(1'000'000, expected_root));
    while (!client.rqs.empty()) {
        monad_statesync_server_run_once(server);
    }
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));

    monad_statesync_client_context_destroy(cctx);
    monad_statesync_server_destroy(server);
    std::filesystem::remove(ctmp);
    std::filesystem::remove(stmp);
}

TEST(StateSync, sync_empty)
{
    auto const ctmp = tmp_dbname();
    auto const stmp = tmp_dbname();
    char const *const cdbname = ctmp.c_str();
    char const *const sdbname = stmp.c_str();

    monad_statesync_client client;
    auto *const cctx = monad_statesync_client_context_create(
        &cdbname, 1, genesis.c_str(), &client, &statesync_send_request);

    OnDiskMachine machine;
    mpt::Db db{
        machine, OnDiskDbConfig{.append = true, .dbname_paths = {sdbname}}};
    TrieDb tdb{db};
    tdb.set_block_number(1'000'000);
    tdb.commit(StateDeltas{}, Code{});
    monad_statesync_server_context sctx{tdb};
    mpt::Db ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {sdbname}}};
    sctx.ro = &ro;
    monad_statesync_server_network net{.client = &client, .cctx = cctx};
    auto *const server = monad_statesync_server_create(
        &sctx,
        &net,
        &statesync_server_recv,
        &statesync_server_send_upsert,
        &statesync_server_send_done);

    monad_statesync_client_handle_target(
        cctx, make_target(1'000'000, NULL_ROOT));
    while (!client.rqs.empty()) {
        monad_statesync_server_run_once(server);
    }
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));

    monad_statesync_client_context_destroy(cctx);
    monad_statesync_server_destroy(server);
    std::filesystem::remove(ctmp);
    std::filesystem::remove(stmp);
}
