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

#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_server.h>
#include <category/statesync/statesync_server_context.hpp>
#include <category/statesync/statesync_version.h>
#include <test_resource_data.h>

#include <ethash/keccak.hpp>
#include <gtest/gtest.h>

#include <deque>
#include <filesystem>
#include <fstream>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

struct monad_statesync_client
{
    std::deque<monad_sync_request> rqs{};
    bool success{true};
};

struct monad_statesync_server_network
{
    monad_statesync_client *client;
    monad_statesync_client_context *cctx;
    byte_string buf;
};

namespace
{
    GenesisState const GENESIS_STATE = EthereumMainnet{}.get_genesis_state();

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
        net->client->success &= done.success;
        if (done.success) {
            monad_statesync_client_handle_done(net->cctx, done);
        }
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
        mpt::AsyncIOContext io_ctx;
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
            , io_ctx{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {sdbname}}}
            , ro{io_ctx}
        {
            sctx.ro = &ro;
        }

        void init()
        {
            char const *const str = cdbname.c_str();
            cctx = monad_statesync_client_context_create(
                &str,
                1,
                static_cast<unsigned>(get_nprocs() - 1),
                &client,
                &statesync_send_request);
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

TEST_F(StateSyncFixture, sync_from_latest)
{
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    {
        OnDiskMachine machine;
        mpt::Db db{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb tdb{db};
        uint64_t const block_number = N - 257;
        load_header(
            db.load_root_for_version(block_number),
            db,
            BlockHeader{.number = block_number});
        for (size_t i = N - 256; i < N; ++i) {
            BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
            tdb.set_block_and_prefix(i - 1);
            commit_sequential(tdb, {}, {}, hdr);
            parent_hash = to_bytes(
                keccak256(rlp::encode_block_header(tdb.read_eth_header())));
        }
        load_db(tdb, N);
        // commit some proposal to client db
        tdb.set_block_and_prefix(N);
        tdb.commit({}, {}, bytes32_t{N + 1}, BlockHeader{.number = N + 1});
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
        uint64_t const block_number = N - 257;
        load_header(
            sdb.load_root_for_version(block_number),
            sdb,
            BlockHeader{.number = block_number});
        for (size_t i = N - 256; i < N; ++i) {
            stdb.set_block_and_prefix(i - 1);
            commit_sequential(
                stdb,
                {},
                {},
                BlockHeader{.parent_hash = parent_hash, .number = i});
            parent_hash = to_bytes(
                keccak256(rlp::encode_block_header(stdb.read_eth_header())));
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
    ctdb.set_block_and_prefix(cdb.get_latest_finalized_version());
    EXPECT_EQ(ctdb.get_block_number(), 1'000'000);
    EXPECT_TRUE(ctdb.read_account(ADDR_A).has_value());
    auto const a_icode = ctdb.read_code(A_CODE_HASH);
    EXPECT_EQ(byte_string_view(a_icode->code(), a_icode->size()), A_CODE);
    auto const b_icode = ctdb.read_code(B_CODE_HASH);
    EXPECT_EQ(byte_string_view(b_icode->code(), b_icode->size()), B_CODE);
    auto const c_icode = ctdb.read_code(C_CODE_HASH);
    EXPECT_EQ(byte_string_view(c_icode->code(), c_icode->size()), C_CODE);
    auto const d_icode = ctdb.read_code(D_CODE_HASH);
    EXPECT_EQ(byte_string_view(d_icode->code(), d_icode->size()), D_CODE);
    auto const e_icode = ctdb.read_code(E_CODE_HASH);
    EXPECT_EQ(byte_string_view(e_icode->code(), e_icode->size()), E_CODE);
    auto const h_icode = ctdb.read_code(H_CODE_HASH);
    EXPECT_EQ(byte_string_view(h_icode->code(), h_icode->size()), H_CODE);

    auto find_res = cdb.find(
        cdb.load_root_for_version(N),
        concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE),
        N);
    ASSERT_TRUE(find_res.has_value());
    auto raw = find_res.value().node->value();
    auto const hdr = rlp::decode_block_header(raw);
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
        load_genesis_state(GENESIS_STATE, tdb);
        // commit some proposal to client db
        tdb.commit({}, {}, NULL_HASH_BLAKE3, BlockHeader{.number = 1});
        load_genesis_state(GENESIS_STATE, stdb);
        init();
    }
    ASSERT_TRUE(stdb.get_root() != nullptr);
    auto const res = sdb.find(
        stdb.get_root(), concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE), 0);
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
        commit_sequential(
            sctx,
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            hdr1);
        EXPECT_EQ(stdb.read_eth_header(), hdr1);
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
        commit_sequential(
            sctx,
            StateDeltas{
                {ADDR1,
                 {.account = {acct, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
            Code{},
            hdr2);
        EXPECT_EQ(stdb.read_eth_header(), hdr2);
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
        auto const icode = vm::make_shared_intercode(code);
        commit_sequential(
            sctx,
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
            Code{{code_hash, icode}},
            hdr3);
        EXPECT_EQ(stdb.read_eth_header(), hdr3);
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
        commit_sequential(
            sctx,
            StateDeltas{
                {ADDR1,
                 {.account = {acct, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {0x0000000000000013370000000000000000000000000000000000000000000003_bytes32,
                         {}}}}}}},
            Code{},
            hdr4);
        EXPECT_EQ(stdb.read_eth_header(), hdr4);
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
        commit_sequential(
            sctx,
            StateDeltas{
                {ADDR1,
                 {.account = {old, acct},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}},
            Code{},
            hdr5);
        EXPECT_EQ(stdb.read_eth_header(), hdr5);
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
        commit_sequential(
            sctx,
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            hdr6);
        EXPECT_EQ(stdb.read_eth_header(), hdr6);
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

    // find transaction trie
    mpt::RODb cdb{ReadOnlyOnDiskDbConfig{.dbname_paths = {cdbname}}};
    for (auto const nibble :
         {RECEIPT_NIBBLE,
          TRANSACTION_NIBBLE,
          WITHDRAWAL_NIBBLE,
          OMMER_NIBBLE,
          TX_HASH_NIBBLE,
          BLOCK_HASH_NIBBLE,
          CALL_FRAME_NIBBLE}) {
        EXPECT_FALSE(cdb.find(concat(FINALIZED_NIBBLE, nibble), hdr6.number)
                         .has_value());
    }
}

TEST_F(StateSyncFixture, deletion_proposal)
{
    {
        OnDiskMachine machine;
        mpt::Db db{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb tdb{db};
        load_genesis_state(GENESIS_STATE, tdb);
        load_genesis_state(GENESIS_STATE, stdb);
        init();
    }
    ASSERT_TRUE(stdb.get_root() != nullptr);
    auto const res = sdb.find(
        stdb.get_root(), concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE), 0);
    ASSERT_TRUE(res.has_value() && res.value().is_valid());
    // delete ADDR1 on one fork
    {
        constexpr auto ADDR1 =
            0x000d836201318ec6899a67540690382780743280_address;
        auto const acct = sctx.read_account(ADDR1);
        ASSERT_TRUE(acct.has_value());
        sctx.set_block_and_prefix(0);
        sctx.commit(
            StateDeltas{{ADDR1, {.account = {acct, std::nullopt}}}},
            Code{},
            bytes32_t{1},
            BlockHeader{.number = 1});
    }
    // delete ADDR2 on another
    {
        constexpr auto ADDR2 =
            0x001762430ea9c3a26e5749afdb70da5f78ddbb8c_address;
        auto const acct = sctx.read_account(ADDR2);
        ASSERT_TRUE(acct.has_value());
        sctx.set_block_and_prefix(0);
        sctx.commit(
            StateDeltas{{ADDR2, {.account = {acct, std::nullopt}}}},
            Code{},
            bytes32_t{2},
            BlockHeader{.number = 1});
    }
    sctx.finalize(1, bytes32_t{2});

    sctx.set_block_and_prefix(1, bytes32_t{1});
    auto const bad_header = sctx.read_eth_header();

    sctx.set_block_and_prefix(1, bytes32_t{2});
    auto const finalized_header = sctx.read_eth_header();

    EXPECT_NE(finalized_header.state_root, bad_header.state_root);
    handle_target(cctx, finalized_header);
    run();

    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_one_account)
{
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    load_header(
        sdb.load_root_for_version(N - 257),
        sdb,
        BlockHeader{.number = N - 257});
    for (size_t i = N - 256; i < N; ++i) {
        stdb.set_block_and_prefix(i - 1);
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    commit_sequential(
        stdb,
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
    load_header(
        sdb.load_root_for_version(N - 257),
        sdb,
        BlockHeader{.number = N - 257});
    for (size_t i = N - 256; i < N; ++i) {
        stdb.set_block_and_prefix(i - 1);
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    commit_sequential(
        stdb, StateDeltas{}, Code{}, BlockHeader{.number = 1'000'000});
    init();
    handle_target(cctx, BlockHeader{.parent_hash = parent_hash, .number = N});
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_client_has_proposals)
{
    {
        // init client DB
        OnDiskMachine machine;
        mpt::Db db{
            machine, OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb tdb{db};
        tdb.reset_root(load_header({}, db, BlockHeader{.number = 0}), 0);
        for (uint64_t n = 1; n <= 249; ++n) {
            tdb.commit({}, {}, bytes32_t{n}, BlockHeader{.number = n});
        }
    }

    constexpr auto N = 300;
    bytes32_t parent_hash{NULL_HASH};
    {
        // init server db
        load_header(
            sdb.load_root_for_version(N - 257),
            sdb,
            BlockHeader{.number = N - 257});
        for (size_t i = N - 256; i < N; ++i) {
            BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
            stdb.set_block_and_prefix(i - 1);
            commit_sequential(stdb, {}, {}, hdr);
            parent_hash = to_bytes(
                keccak256(rlp::encode_block_header(stdb.read_eth_header())));
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
}

TEST_F(StateSyncFixture, account_updated_after_storage)
{
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
        commit_sequential(stdb, {}, {}, hdr);
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    BlockHeader hdr{.parent_hash = parent_hash, .number = 100};
    commit_sequential(
        sctx,
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
    parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr = BlockHeader{.parent_hash = parent_hash, .number = 101};
    commit_sequential(sctx, {}, {}, hdr);
    parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr = BlockHeader{.parent_hash = parent_hash, .number = 102};
    commit_sequential(
        sctx,
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
        commit_sequential(stdb, {}, {}, hdr);
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    BlockHeader hdr{.parent_hash = parent_hash, .number = 100};
    commit_sequential(
        sctx,
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
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr.number = 101;
    commit_sequential(sctx, {}, {}, hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr.number = 102;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, std::nullopt},
                 .storage = {}}}},
        Code{},
        hdr);
    EXPECT_EQ(sctx.state_root(), NULL_ROOT);
    init();
    hdr.state_root = NULL_ROOT;
    handle_target(cctx, hdr);
}

TEST_F(StateSyncFixture, account_deleted_and_prefix_skipped)
{
    init();
    BlockHeader hdr{.parent_hash = NULL_HASH};
    commit_sequential(sctx, StateDeltas{}, Code{}, hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 1;
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 100}},
                 .storage = {}}}},
        Code{},
        hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 2;
    hdr.state_root = NULL_ROOT;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {Account{.balance = 100}, std::nullopt},
                 .storage = {}}}},
        Code{},
        hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    client.rqs.clear();

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 3;
    hdr.state_root = NULL_ROOT;
    commit_sequential(sctx, StateDeltas{}, Code{}, hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, delete_updated_account)
{
    init();
    BlockHeader hdr{.parent_hash = NULL_HASH};
    commit_sequential(sctx, StateDeltas{}, Code{}, hdr);

    Account const a{.balance = 100, .incarnation = Incarnation{1, 0}};

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    hdr.number = 1;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}},
        Code{},
        hdr);
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.state_root =
        0x5c906b969120501ff89a0ba246bc366c458b0ee101b075a7b91791a3dcf79844_bytes32;
    hdr.number = 2;
    commit_sequential(
        sctx,
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

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.state_root = NULL_ROOT;
    hdr.number = 3;
    commit_sequential(
        sctx,
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
    uint64_t const block_number = 1'000'000 - 257;
    load_header(
        sdb.load_root_for_version(block_number),
        sdb,
        BlockHeader{.number = block_number});
    for (size_t i = 1'000'000 - 256; i < 1'000'000; ++i) {
        stdb.set_block_and_prefix(i - 1);
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }

    BlockHeader hdr{
        .parent_hash = parent_hash,
        .state_root =
            0x92c33474d175fb59002e90f3625f9850b8305519318701e61f3fd8341d63983d_bytes32,
        .number = 1'000'000};
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, a},
                 .storage =
                     {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}},
                      {bytes32_t{1}, {bytes32_t{}, bytes32_t{64}}}}}}},
        Code{},
        hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 1'000'001;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A, StateDelta{.account = {a, std::nullopt}, .storage = {}}}},
        Code{},
        hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 1'000'002;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, a},
                 .storage = {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}}}}}},
        Code{},
        hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    hdr.number = 1'000'003;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {a, a},
                 .storage = {{bytes32_t{}, {bytes32_t{64}, bytes32_t{}}}}}}},
        Code{},
        hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, update_contract_twice)
{
    init();

    BlockHeader hdr{.parent_hash = NULL_HASH, .number = 0};
    commit_sequential(sctx, StateDeltas{}, Code{}, hdr);

    constexpr auto ADDR1 = 0x5353535353535353535353535353535353535353_address;
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    auto const code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                       "ffffffffffffffffffffff0160005500")
            .value();
    auto const code_hash = to_bytes(keccak256(code));
    auto const icode = vm::make_shared_intercode(code);

    Account const a{
        .balance = 1337,
        .code_hash = code_hash,
        .nonce = 1,
        .incarnation = Incarnation{1, 0}};

    hdr.state_root =
        0x3dda8f21af5ec3d4caea2b3b2bddd988e3f1ff1fbfdbaa87a6477bbfce356d26_bytes32;
    hdr.number = 1;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR1,
             {.account = {std::nullopt, a},
              .storage =
                  {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                    {{},
                     0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}

        },
        Code{{code_hash, icode}},
        hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    run();

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.state_root =
        0xca4adc8c322ed636a12f74b72d88536795f70e74c8c9b6448ad57058a57664af_bytes32;
    hdr.number = 2;
    commit_sequential(
        sctx,
        StateDeltas{
            {ADDR1,
             {.account = {a, a},
              .storage =
                  {{0x0000000000000000000000000000000000000000000000000000000011110000_bytes32,
                    {{},
                     0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}

        },
        Code{},
        hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    run();

    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, handle_request_from_bad_block)
{
    load_header(sdb.load_root_for_version(0), sdb, BlockHeader{.number = 0});
    load_header(sdb.load_root_for_version(1), sdb, BlockHeader{.number = 1});
    init();
    handle_target(cctx, BlockHeader{.number = 1});
    run();
    EXPECT_FALSE(client.success);
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
    uint64_t const block_number = 1'000'000 - 257;
    load_header(
        sdb.load_root_for_version(block_number),
        sdb,
        BlockHeader{.number = block_number});
    for (size_t i = 1'000'000 - 256; i < 1'000'000; ++i) {
        stdb.set_block_and_prefix(i - 1);
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }

    BlockHeader const hdr{
        .parent_hash = parent_hash,
        .state_root =
            0x50510e4f9ecc40a8cc5819bdc589a0e09c172ed268490d5f755dba939f7e8997_bytes32,
        .number = N};
    StateDeltas deltas{v.begin(), v.end()};
    commit_sequential(stdb, deltas, Code{}, hdr);
    init();
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
    quill::flush();
}

TEST(Deletions, history_length)
{
    auto const deletions = std::make_unique<FinalizedDeletions>();
    for (uint64_t i = 1; i <= MAX_ENTRIES + 1; ++i) {
        Deletion const deletion{.address = Address{i}};
        deletions->write(i, {deletion});
        std::vector<Deletion> result;
        auto const fn = [&result](auto const &deletion) {
            result.push_back(deletion);
        };
        bool const success = deletions->for_each(i, fn);
        EXPECT_TRUE(success);
        ASSERT_EQ(result.size(), 1);
        EXPECT_EQ(result[0], deletion);
    }
    bool const success = deletions->for_each(1, {});
    EXPECT_FALSE(success);
}

TEST(Deletions, max_deletions)
{
    auto const deletions = std::make_unique<FinalizedDeletions>();
    deletions->write(1, {});
    for (uint64_t i = 2; i <= 101; ++i) {
        Deletion const deletion{.address = Address{i}};
        deletions->write(i, {deletion});
    }
    std::vector<Deletion> to{MAX_DELETIONS - 100};
    for (uint64_t i = 0; i < to.size(); ++i) {
        to[i] = Deletion{.key = bytes32_t{i}};
    }
    deletions->write(102, to);

    // Check that everything fits
    std::vector<Deletion> result;
    auto const fn = [&result](auto const &deletion) {
        result.push_back(deletion);
    };
    bool success = deletions->for_each(1, fn);
    EXPECT_TRUE(success);
    EXPECT_TRUE(result.empty());

    for (uint64_t i = 2; i <= 101; ++i) {
        result.clear();
        success = deletions->for_each(i, fn);
        EXPECT_TRUE(success);
        ASSERT_EQ(result.size(), 1);
        EXPECT_EQ(result[0], Deletion{.address = Address{i}});
    }

    result.clear();
    success = deletions->for_each(102, fn);
    EXPECT_TRUE(success);
    EXPECT_EQ(result, to);

    // now exceed the max and check that history is pruned
    std::vector<Deletion> to_103{10};
    for (uint64_t i = 0; i < to_103.size(); ++i) {
        to_103[i] = Deletion{.key = bytes32_t{i}};
    }
    deletions->write(103, to_103);

    for (uint64_t i = 1; i <= 11; ++i) {
        success = deletions->for_each(i, fn);
        EXPECT_FALSE(success);
    }

    for (uint64_t i = 12; i <= 101; ++i) {
        result.clear();
        success = deletions->for_each(i, fn);
        EXPECT_TRUE(success);
        ASSERT_EQ(result.size(), 1);
        EXPECT_EQ(result[0], Deletion{.address = Address{i}});
    }

    result.clear();
    success = deletions->for_each(102, fn);
    EXPECT_TRUE(success);
    EXPECT_EQ(result, to);

    result.clear();
    success = deletions->for_each(103, fn);
    EXPECT_TRUE(success);
    EXPECT_EQ(result, to_103);

    // now prune everything
    std::vector<Deletion> to_104{MAX_DELETIONS};
    for (uint64_t i = 0; i < to_104.size(); ++i) {
        to_104[i] = Deletion{.address = Address{i}};
    }
    deletions->write(104, to_104);
    for (uint64_t i = 1; i <= 103; ++i) {
        success = deletions->for_each(i, fn);
        EXPECT_FALSE(success);
    }
    result.clear();
    success = deletions->for_each(104, fn);
    EXPECT_TRUE(success);
    EXPECT_EQ(result, to_104);
}

TEST(Deletions, max_deletions_replenish)
{
    auto const deletions = std::make_unique<FinalizedDeletions>();

    // use 10 deletions
    uint64_t i = 1;
    for (; i <= 10; ++i) {
        Deletion const deletion{.address = Address{i}};
        deletions->write(i, {deletion});
    }
    for (; i <= MAX_ENTRIES; ++i) {
        deletions->write(i, {});
    }

    // overwriting replenishes 10 deletions
    for (; i <= MAX_ENTRIES + 10; ++i) {
        deletions->write(i, {});
    }

    // should be able to write all without pruning
    std::vector<Deletion> const to{MAX_DELETIONS};
    deletions->write(i, to);

    for (uint64_t j = i - MAX_ENTRIES + 1; j <= i; ++j) {
        bool const success = deletions->for_each(j, [](auto const &) {});
        EXPECT_TRUE(success);
    }
}

TEST(Deletions, exceed_max_deletions)
{
    auto const deletions = std::make_unique<FinalizedDeletions>();
    for (uint64_t i = 1; i <= 10; ++i) {
        Deletion const deletion{.address = Address{i}};
        deletions->write(i, {deletion});
    }
    std::vector<Deletion> const to{MAX_DELETIONS + 1};
    deletions->write(11, to);

    // everything blown away
    for (uint64_t i = 1; i <= 11; ++i) {
        bool const success = deletions->for_each(i, [](auto const &) {});
        EXPECT_FALSE(success);
    }

    // write something
    std::vector<Deletion> const to2{MAX_DELETIONS};
    deletions->write(12, to2);

    bool const success = deletions->for_each(12, [](auto const &) {});
    EXPECT_TRUE(success);
}

// Unit tests for request validation logic
TEST_F(StateSyncFixture, validation_prefix_bytes_too_large)
{
    // Set up a valid database state
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        if (i > 0) {
            stdb.set_block_and_prefix(i - 1);
        }
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    init();

    monad_sync_request rq{
        .prefix = 0,
        .prefix_bytes = 9, // exceeds maximum of 8 - INVALID
        .target = 99,
        .from = 0,
        .until = 99,
        .old_target = INVALID_BLOCK_NUM};

    client.rqs.push_back(rq);
    monad_statesync_server_run_once(server);
    // Should fail due to validation, not due to missing data
    EXPECT_FALSE(client.success);
}

TEST_F(StateSyncFixture, validation_target_invalid)
{
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        if (i > 0) {
            stdb.set_block_and_prefix(i - 1);
        }
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    init();

    monad_sync_request rq{
        .prefix = 0,
        .prefix_bytes = 8,
        .target = INVALID_BLOCK_NUM, // invalid target
        .from = 0,
        .until = 99,
        .old_target = INVALID_BLOCK_NUM};

    client.rqs.push_back(rq);
    monad_statesync_server_run_once(server);
    EXPECT_FALSE(client.success);
}

TEST_F(StateSyncFixture, validation_from_greater_than_until)
{
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        if (i > 0) {
            stdb.set_block_and_prefix(i - 1);
        }
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    init();

    monad_sync_request rq{
        .prefix = 0,
        .prefix_bytes = 8,
        .target = 99,
        .from = 50,
        .until = 40, // from > until - INVALID
        .old_target = INVALID_BLOCK_NUM};

    client.rqs.push_back(rq);
    monad_statesync_server_run_once(server);
    EXPECT_FALSE(client.success);
}

TEST_F(StateSyncFixture, validation_until_greater_than_target)
{
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        if (i > 0) {
            stdb.set_block_and_prefix(i - 1);
        }
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    init();

    monad_sync_request rq{
        .prefix = 0,
        .prefix_bytes = 8,
        .target = 99,
        .from = 0,
        .until = 100, // until > target - INVALID
        .old_target = INVALID_BLOCK_NUM};

    client.rqs.push_back(rq);
    monad_statesync_server_run_once(server);
    EXPECT_FALSE(client.success);
}

TEST_F(StateSyncFixture, validation_old_target_greater_than_target)
{
    bytes32_t parent_hash{NULL_HASH};
    for (size_t i = 0; i < 100; ++i) {
        if (i > 0) {
            stdb.set_block_and_prefix(i - 1);
        }
        commit_sequential(
            stdb, {}, {}, BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    init();

    monad_sync_request rq{
        .prefix = 0,
        .prefix_bytes = 8,
        .target = 50,
        .from = 0,
        .until = 50,
        .old_target = 51}; // old_target > target - INVALID

    client.rqs.push_back(rq);
    monad_statesync_server_run_once(server);
    EXPECT_FALSE(client.success);
}
