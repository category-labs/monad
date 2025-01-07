#include <monad/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>
#include <monad/statesync/statesync_version.h>
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

    void handle_target(
        monad_statesync_client_context *const ctx, BlockHeader const &hdr)
    {
        auto const rlp = rlp::encode_block_header(hdr);
        monad_statesync_client_handle_target(ctx, rlp.data(), rlp.size());
    }

    ssize_t statesync_server_recv(
        monad_statesync_server_network *const net, unsigned char *const buf,
        size_t const len)
    {
        if (len == 1) {
            constexpr auto MSG_TYPE = SYNC_TYPE_REQUEST;
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
        // TODO: prefixes have different protocols
        MONAD_ASSERT(monad_statesync_client_handle_upsert(
            net->cctx, 0, type, net->buf.data(), net->buf.size()));
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
            for (size_t i = 0; i < monad_statesync_client_prefixes(); ++i) {
                monad_statesync_client_handle_new_peer(
                    cctx, i, monad_statesync_version());
            }
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
    handle_target(
        cctx,
        BlockHeader{
            .state_root =
                0xd7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544_bytes32});
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_from_latest)
{
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    {
        OnDiskMachine machine;
        mpt::Db db{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb tdb{db};
        for (size_t i = N - 256; i < N; ++i) {
            BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
            parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
            tdb.commit({}, {}, hdr);
        }
        load_db(tdb, N);
        init();
    }
    handle_target(
        cctx,
        BlockHeader{
            .parent_hash = parent_hash,
            .state_root =
                0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32,
            .number = N});
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_from_empty)
{
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    {
        for (size_t i = N - 256; i < N; ++i) {
            BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
            parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
            stdb.commit({}, {}, hdr);
        }
        load_db(stdb, N);
        init();
    }
    BlockHeader const tgrt{
        .parent_hash = parent_hash,
        .state_root =
            0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32,
        .number = N};
    handle_target(cctx, tgrt);
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

    auto raw = cdb.get(concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE), N);
    ASSERT_TRUE(raw.has_value());
    auto const hdr = rlp::decode_block_header(raw.value());
    ASSERT_TRUE(hdr.has_value());
    EXPECT_EQ(hdr.value(), tgrt);
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
    auto const root = sdb.load_root_for_version(0);
    ASSERT_TRUE(root.is_valid());
    auto const res =
        sdb.find(root, concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE), 0);
    ASSERT_TRUE(res.has_value() && res.value().is_valid());
    BlockHeader const hdr1{
        .parent_hash = to_bytes(keccak256(res.value().node->value())),
        .state_root =
            0x5d651a344741e37c613b580048934ae0deb58b72b542b61416cf7d1fb81d5a79_bytes32,
        .number = 1};
    // delete existing account
    {
        constexpr auto ADDR1 =
            0x000d836201318ec6899a67540690382780743280_address;
        auto const acct = stdb.read_account(ADDR1);
        MONAD_ASSERT(acct.has_value());
        sctx.commit(
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            hdr1);
    }
    BlockHeader const hdr2{
        .parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr1))),
        .state_root =
            0xd1afa4d8e4546cd3ca0314f2ea5ed7c2de22162b2d72b0ca3f56bcfa551e9e5f_bytes32,
        .number = 2};
    // new storage to existing account
    {
        constexpr auto ADDR1 =
            0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
        auto const acct = stdb.read_account(ADDR1);
        sctx.commit(
            StateDeltas{
                {ADDR1,
                 {.account = {acct, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
            Code{},
            hdr2);
    }
    BlockHeader const hdr3{
        .parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr2))),
        .state_root =
            0x1922e617443693307d169df71f44688795793a91c4bf40742765c096e00413d7_bytes32,
        .number = 3};
    // add new smart contract
    {
        constexpr auto ADDR1 =
            0x5353535353535353535353535353535353535353_address;
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
            hdr3,
            {});
    }
    BlockHeader const hdr4{
        .parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr3))),
        .state_root =
            0x589b5012c41144a33447c07b0cc1f3108181774b7f1eec1fa0f466ffa9bc74b3_bytes32,
        .number = 4};
    // delete storage
    {
        constexpr auto ADDR1 =
            0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
        auto const acct = stdb.read_account(ADDR1);
        sctx.commit(
            StateDeltas{
                {ADDR1,
                 {.account = {acct, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {0x0000000000000013370000000000000000000000000000000000000000000003_bytes32,
                         {}}}}}}},
            Code{},
            hdr4);
    }
    BlockHeader const hdr5{
        .parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr4))),
        .state_root =
            0x1922e617443693307d169df71f44688795793a91c4bf40742765c096e00413d7_bytes32,
        .number = 5};
    // account incarnation
    {
        constexpr auto ADDR1 =
            0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
        auto const old = stdb.read_account(ADDR1);
        auto acct = old;
        acct->incarnation = Incarnation{5, 0};
        sctx.commit(
            StateDeltas{
                {ADDR1,
                 {.account = {old, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
            Code{},
            hdr5);
    }
    BlockHeader const hdr6{
        .parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr5))),
        .state_root =
            0xd1afa4d8e4546cd3ca0314f2ea5ed7c2de22162b2d72b0ca3f56bcfa551e9e5f_bytes32,
        .number = 6};
    // delete smart contract
    {
        constexpr auto ADDR1 =
            0x5353535353535353535353535353535353535353_address;
        auto const acct = stdb.read_account(ADDR1);
        MONAD_ASSERT(acct.has_value());
        sctx.commit(
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            hdr6);
    }

    handle_target(cctx, hdr1);
    run();

    handle_target(cctx, hdr2);
    run();

    handle_target(cctx, hdr3);
    run();

    handle_target(cctx, hdr4);
    run();

    handle_target(cctx, hdr5);
    run();

    handle_target(cctx, hdr6);
    run();

    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, ignore_unused_code)
{
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    {
        for (size_t i = N - 256; i < N; ++i) {
            BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
            parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
            stdb.commit({}, {}, hdr);
        }
        load_db(stdb, N);
        init();
    }

    auto const code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                       "ffffffffffffffffffffffff")
            .value();
    auto const code_hash = to_bytes(keccak256(code));
    handle_target(
        cctx,
        BlockHeader{
            .parent_hash = parent_hash,
            .state_root =
                0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32,
            .number = N});
    // send some random code
    statesync_server_send_upsert(
        &net, SYNC_TYPE_UPSERT_CODE, code.data(), code.size(), nullptr, 0);
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
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = N - 256; i < N; ++i) {
        BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
        parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
        stdb.commit({}, {}, hdr);
    }
    stdb.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage = {}}}},
        Code{},
        BlockHeader{.number = N});
    init();
    handle_target(
        cctx,
        BlockHeader{
            .parent_hash = parent_hash,
            .state_root = stdb.state_root(),
            .number = N});
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_empty)
{
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = N - 256; i < N; ++i) {
        BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
        parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
        stdb.commit({}, {}, hdr);
    }
    stdb.commit(StateDeltas{}, Code{}, BlockHeader{.number = 1'000'000});
    init();
    handle_target(cctx, BlockHeader{.parent_hash = parent_hash, .number = N});
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, account_updated_after_storage)
{
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
        parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
        stdb.commit({}, {}, hdr);
    }
    BlockHeader hdr{.parent_hash = parent_hash, .number = 100};
    parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
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
        hdr);

    hdr = BlockHeader{.parent_hash = parent_hash, .number = 101};
    parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    sctx.commit({}, {}, hdr, {});

    hdr = BlockHeader{.parent_hash = parent_hash, .number = 102};
    parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, Account{.balance = 200}},
                 .storage = {}}}},
        Code{},
        hdr);
    init();
    hdr.state_root = stdb.state_root();
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, account_deleted_after_storage)
{
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
        parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
        stdb.commit({}, {}, hdr);
    }
    BlockHeader hdr{.parent_hash = parent_hash, .number = 100};
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
        hdr);
    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.number = 101;
    sctx.commit({}, {}, hdr, {});
    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.number = 102;
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, std::nullopt},
                 .storage = {}}}},
        Code{},
        hdr);
    init();
    hdr.state_root = NULL_ROOT;
    handle_target(cctx, hdr);
}

TEST_F(StateSyncFixture, account_deleted_and_prefix_skipped)
{
    init();
    BlockHeader hdr{.parent_hash = NULL_HASH};
    sctx.commit(StateDeltas{}, Code{}, hdr);
    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.number = 1;
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage = {}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.number = 2;
    hdr.state_root = NULL_ROOT;
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, std::nullopt},
                 .storage = {}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    client.rqs.clear();

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.number = 3;
    hdr.state_root = NULL_ROOT;
    sctx.commit(StateDeltas{}, Code{}, hdr);
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, delete_updated_account)
{
    init();
    BlockHeader hdr{.parent_hash = NULL_HASH};
    sctx.commit(StateDeltas{}, Code{}, hdr);

    Account const a{.balance = 100, .incarnation = Incarnation{1, 0}};

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    hdr.number = 1;
    sctx.commit(
        StateDeltas{
            {ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.state_root =
        0x5c906b969120501ff89a0ba246bc366c458b0ee101b075a7b91791a3dcf79844_bytes32;
    hdr.number = 2;
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {a, a},
                 .storage = {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}}}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    client.rqs.pop_front();
    while (!client.rqs.empty()) {
        monad_statesync_server_run_once(server);
    }

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.state_root = NULL_ROOT;
    hdr.number = 3;
    sctx.commit(
        StateDeltas{
            {ADDR_A, StateDelta{.account = {a, std::nullopt}, .storage = {}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, delete_storage_after_account_deletion)
{
    init();

    Account const a{.balance = 100, .incarnation = Incarnation{1, 0}};

    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 1'000'000 - 256; i < 1'000'000; ++i) {
        BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
        parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
        stdb.commit({}, {}, hdr);
    }

    BlockHeader hdr{
        .parent_hash = parent_hash,
        .state_root =
            0x92c33474d175fb59002e90f3625f9850b8305519318701e61f3fd8341d63983d_bytes32,
        .number = 1'000'000};
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, a},
                 .storage =
                     {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}},
                      {bytes32_t{1}, {bytes32_t{}, bytes32_t{64}}}}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.number = 1'000'001;
    sctx.commit(
        StateDeltas{
            {ADDR_A, StateDelta{.account = {a, std::nullopt}, .storage = {}}}},
        Code{},
        hdr);

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.number = 1'000'002;
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, a},
                 .storage = {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}}}}}},
        Code{},
        hdr);

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    hdr.number = 1'000'003;
    sctx.commit(
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {a, a},
                 .storage = {{bytes32_t{}, {bytes32_t{64}, bytes32_t{}}}}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, update_contract_twice)
{
    init();

    BlockHeader hdr{.parent_hash = NULL_HASH};
    sctx.commit(StateDeltas{}, Code{}, hdr);

    constexpr auto ADDR1 = 0x5353535353535353535353535353535353535353_address;

    auto const code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                       "ffffffffffffffffffffff0160005500")
            .value();
    auto const code_hash = to_bytes(keccak256(code));
    auto const code_analysis = std::make_shared<CodeAnalysis>(analyze(code));

    Account const a{
        .balance = 1337,
        .code_hash = code_hash,
        .nonce = 1,
        .incarnation = Incarnation{1, 0}};

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.state_root =
        0x3dda8f21af5ec3d4caea2b3b2bddd988e3f1ff1fbfdbaa87a6477bbfce356d26_bytes32;
    hdr.number = 1;
    sctx.commit(
        StateDeltas{
            {ADDR1,
             {.account = {std::nullopt, a},
              .storage =
                  {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                    {{},
                     0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}

        },
        Code{{code_hash, code_analysis}},
        hdr,
        {});
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
    hdr.state_root =
        0xca4adc8c322ed636a12f74b72d88536795f70e74c8c9b6448ad57058a57664af_bytes32;
    hdr.number = 2;
    sctx.commit(
        StateDeltas{
            {ADDR1,
             {.account = {a, a},
              .storage =
                  {{0x0000000000000000000000000000000000000000000000000000000011110000_bytes32,
                    {{},
                     0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}

        },
        Code{},
        hdr,
        {});
    handle_target(cctx, hdr);
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

    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 1'000'000 - 256; i < 1'000'000; ++i) {
        BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
        parent_hash = to_bytes(keccak256(rlp::encode_block_header(hdr)));
        stdb.commit({}, {}, hdr);
    }

    BlockHeader const hdr{
        .parent_hash = parent_hash,
        .state_root =
            0x50510e4f9ecc40a8cc5819bdc589a0e09c172ed268490d5f755dba939f7e8997_bytes32,
        .number = 1'000'000};
    StateDeltas deltas{v.begin(), v.end()};
    stdb.commit(deltas, Code{}, hdr);
    init();
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}
