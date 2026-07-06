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
#include <category/core/hex.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/chain/chain_factory.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/state_machine_init.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db_metadata_context.hpp>
#include <category/mpt/detail/timeline.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/trie.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_server.h>
#include <category/statesync/statesync_server_context.hpp>
#include <category/statesync/statesync_version.h>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <test_resource_data.h>

#include <ethash/keccak.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>

#include <array>
#include <deque>
#include <filesystem>
#include <fstream>
#include <memory>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test;

namespace monad::mpt::test
{
    // Friend-of-Db accessor: lets the temp-db helper stamp the persisted
    // state_machine_kind on a fresh pool, simulating what monad-mpt --create
    // --state-machine ethereum does in production.
    struct DbAccessor
    {
        static UpdateAux &aux(Db &db)
        {
            return const_cast<UpdateAux &>(db.aux());
        }
    };
}

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
    byte_string deferred_account;
    bool defer_first_account_until_storage{};
    bool drop_first_account{};
    bool corrupt_first_account_domain_suffix{};
    bool account_was_dropped{};
    bool upsert_was_rejected{};
};

namespace
{
    GenesisState const GENESIS_STATE = EthereumMainnet{}.get_genesis_state();

    std::filesystem::path tmp_dbname()
    {
        monad::register_ethereum_state_machines();
        monad::register_monad_state_machines();
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
        // Stamp the kind so a later open via Db(OnDiskDbConfig const&) — which
        // monad_statesync_client_context uses internally — finds a valid kind.
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
        monad::mpt::test::DbAccessor::aux(db)
            .metadata_ctx()
            .set_state_machine_kind(
                timeline_id::primary, state_machine_kind::ethereum);
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

    bytes32_t header_hash(BlockHeader const &hdr)
    {
        return to_bytes(keccak256(rlp::encode_block_header(hdr)));
    }

    void add_domain_delta(
        DomainStateDeltas &domain_deltas, uint64_t const domain,
        Address const &addr, std::optional<Account> const &old_account,
        std::optional<Account> const &new_account, StorageDeltas storage = {})
    {
        DomainStateDeltas::accessor domain_it{};
        domain_deltas.emplace(
            domain_it, domain, std::make_unique<StateDeltas>());
        StateDeltas::accessor it{};
        domain_it->second->emplace(
            it,
            addr,
            StateDelta{
                .account = {old_account, new_account},
                .storage = std::move(storage)});
    }

    DomainStateDeltas one_domain_delta(
        uint64_t const domain, Address const &addr,
        std::optional<Account> const &old_account,
        std::optional<Account> const &new_account, StorageDeltas storage = {})
    {
        DomainStateDeltas domain_deltas;
        add_domain_delta(
            domain_deltas,
            domain,
            addr,
            old_account,
            new_account,
            std::move(storage));
        return domain_deltas;
    }

    bytes32_t domain_root_with_metadata(
        uint64_t const domain, bool const encoded_metadata, Account const &acct)
    {
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        std::deque<mpt::Update> alloc;
        std::deque<byte_string> bytes_alloc;
        std::deque<hash256> hash_alloc;

        Address const addr{0x1234};
        UpdateList account_list;
        account_list.push_front(alloc.emplace_back(Update{
            .key = hash_alloc.emplace_back(keccak256(addr.bytes)),
            .value = bytes_alloc.emplace_back(encode_account_db(addr, acct)),
            .incarnation = false,
            .next = UpdateList{},
            .version = 1}));

        uint8_t domain_bytes[sizeof(uint64_t)];
        intx::be::store(domain_bytes, domain);
        byte_string const domain_metadata =
            encoded_metadata ? rlp::encode_unsigned(domain) : byte_string{};
        UpdateList domain_list;
        domain_list.push_front(alloc.emplace_back(Update{
            .key = bytes_alloc.emplace_back(domain_bytes, sizeof(domain_bytes)),
            .value = byte_string_view{domain_metadata},
            .incarnation = false,
            .next = std::move(account_list),
            .version = 1}));

        UpdateList table_list;
        table_list.push_front(alloc.emplace_back(Update{
            .key = domain_state_nibbles,
            .value = byte_string_view{},
            .incarnation = false,
            .next = std::move(domain_list),
            .version = 1}));

        UpdateList root_list;
        root_list.push_front(alloc.emplace_back(Update{
            .key = finalized_nibbles,
            .value = byte_string_view{},
            .incarnation = false,
            .next = std::move(table_list),
            .version = 1}));

        auto root = db.upsert({}, std::move(root_list), 1, true);
        auto const res = db.find(
            root,
            concat(
                finalized_nibbles,
                domain_state_nibbles,
                NibblesView{to_byte_string_view(domain_bytes)}),
            1);
        MONAD_ASSERT(res.has_value());
        auto const data = res.value().node->data();
        MONAD_ASSERT(data.size() == sizeof(bytes32_t));
        return to_bytes(data);
    }

    void expect_domain_id_metadata(
        mpt::Db &db, uint64_t const version, uint64_t const domain)
    {
        uint8_t domain_bytes[sizeof(uint64_t)];
        intx::be::store(domain_bytes, domain);
        auto const res = db.find(
            db.load_root_for_version(version),
            concat(
                finalized_nibbles,
                domain_state_nibbles,
                NibblesView{to_byte_string_view(domain_bytes)}),
            version);
        ASSERT_TRUE(res.has_value());
        ASSERT_TRUE(res.value().node->has_value());

        auto raw = res.value().node->value();
        auto const decoded = rlp::decode_unsigned<uint64_t>(raw);
        ASSERT_TRUE(decoded.has_value());
        EXPECT_EQ(decoded.value(), domain);
        EXPECT_TRUE(raw.empty());
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

        auto const deliver = [net](
                                 monad_sync_type const deliver_type,
                                 byte_string const &payload) {
            // TODO: prefixes have different protocols
            MONAD_ASSERT(monad_statesync_client_handle_upsert(
                net->cctx, 0, deliver_type, payload.data(), payload.size()));
        };

        if (type == SYNC_TYPE_UPSERT_ACCOUNT && net->drop_first_account) {
            net->drop_first_account = false;
            net->account_was_dropped = true;
            return;
        }

        if (type == SYNC_TYPE_UPSERT_ACCOUNT &&
            net->corrupt_first_account_domain_suffix) {
            net->corrupt_first_account_domain_suffix = false;
            net->buf += rlp::encode_unsigned(uint64_t{1});
            net->upsert_was_rejected = !monad_statesync_client_handle_upsert(
                net->cctx, 0, type, net->buf.data(), net->buf.size());
            net->client->success &= !net->upsert_was_rejected;
            return;
        }

        if (type == SYNC_TYPE_UPSERT_ACCOUNT &&
            net->defer_first_account_until_storage &&
            net->deferred_account.empty()) {
            net->defer_first_account_until_storage = false;
            net->deferred_account = net->buf;
            return;
        }

        deliver(type, net->buf);
        if (type == SYNC_TYPE_UPSERT_STORAGE &&
            !net->deferred_account.empty()) {
            deliver(SYNC_TYPE_UPSERT_ACCOUNT, net->deferred_account);
            net->deferred_account.clear();
        }
    }

    void statesync_server_send_done(
        monad_statesync_server_network *const net, monad_sync_done const done)
    {
        net->client->success &= done.success;
        if (done.success && net->client->success) {
            monad_statesync_client_handle_done(net->cctx, done);
        }
    }

    // single-timeline server, dual-timeline client
    template <bool MIP_8_ACTIVE>
    struct StateSyncFixtureT : public ::testing::Test
    {
        static std::unique_ptr<OnDiskMachine> make_server_machine()
        {
            if constexpr (MIP_8_ACTIVE) { // if mip_8_is_active, we make server
                                          // primary db page encoded
                return std::make_unique<MonadOnDiskMachine>();
            }
            else {
                return std::make_unique<OnDiskMachine>();
            }
        }

        struct RevisionConfig
        {
            monad_chain_config chain_config;
            uint64_t timestamp;
        };

        // This is THE single place to update when a chain's mip8 activation
        // timestamp changes or MONAD_NEXT is promoted to a concrete revision.
        // Pre-mip8: testnet at timestamp 0 maps to MONAD_ZERO (slot canonical).
        static constexpr RevisionConfig PRE_MIP8{CHAIN_CONFIG_MONAD_TESTNET, 0};
        // Post-mip8: devnet currently maps to MONAD_NEXT for any timestamp
        static constexpr RevisionConfig POST_MIP8{CHAIN_CONFIG_MONAD_DEVNET, 0};

        std::filesystem::path cdbname;
        monad_statesync_client client;
        monad_statesync_client_context *cctx;
        std::filesystem::path sdbname;
        mpt::Db sdb;
        TrieDb stdb;
        monad_statesync_server_context sctx;
        mpt::AsyncIOContext io_ctx;
        mpt::Db ro;
        RevisionConfig const revision_config;
        monad_statesync_server_network net;
        monad_statesync_server *server{};

        static constexpr bool mip_8_is_active = MIP_8_ACTIVE;

        StateSyncFixtureT()
            : cdbname{tmp_dbname()}
            , cctx{nullptr}
            , sdbname{tmp_dbname()}
            , sdb{make_server_machine(),
                  OnDiskDbConfig{.append = true, .dbname_paths = {sdbname}}}
            , stdb{sdb}
            , sctx{stdb}
            , io_ctx{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {sdbname}}}
            , ro{io_ctx}
            , revision_config{MIP_8_ACTIVE ? POST_MIP8 : PRE_MIP8}
        {
            MONAD_ASSERT(MIP_8_ACTIVE == stdb.is_page_encoded());
            sctx.ro = &ro;
            // The client context now requires a secondary timeline to
            // already be active on the client db.
            mpt::Db primary{
                std::make_unique<OnDiskMachine>(),
                OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
            [[maybe_unused]] mpt::Db secondary =
                primary.activate_secondary_timeline(
                    std::make_unique<MonadOnDiskMachine>());
            MONAD_ASSERT(primary.timeline_active(mpt::timeline_id::secondary));
        }

        void init()
        {
            // Production C ABI (monad_statesync_client_context_create) does
            // this; tests that bypass the C ABI and call the C++ ctor
            // directly must populate the registry themselves.
            monad::register_ethereum_state_machines();
            monad::register_monad_state_machines();
            cctx = new monad_statesync_client_context{
                revision_config.chain_config,
                {cdbname},
                std::make_optional(static_cast<unsigned>(get_nprocs() - 1)),
                4,
                &client,
                &statesync_send_request};
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

        monad_revision get_monad_revision() const
        {
            return make_monad_chain(revision_config.chain_config)
                ->get_monad_revision(revision_config.timestamp);
        }

        TrieDb &canonical_client_tdb()
        {
            if constexpr (MIP_8_ACTIVE) {
                MONAD_ASSERT(cctx->secondary_tdb);
                return *cctx->secondary_tdb;
            }
            else {
                return cctx->tdb;
            }
        }

        void set_client_block(uint64_t const block_number)
        {
            cctx->tdb.set_block_and_prefix(block_number);
            MONAD_ASSERT(cctx->secondary_tdb);
            cctx->secondary_tdb->set_block_and_prefix(block_number);
        }

        void restart_client()
        {
            monad_statesync_client_context_destroy(cctx);
            monad_statesync_server_destroy(server);
            cctx = nullptr;
            server = nullptr;
            client = {};
            net = {};
            init();
        }

        ~StateSyncFixtureT()
        {
            monad_statesync_client_context_destroy(cctx);
            monad_statesync_server_destroy(server);
            std::filesystem::remove(cdbname);
            std::filesystem::remove(sdbname);
        }
    };

    // Slot-encoded server primary for pre-mip8 fork.
    using StateSyncFixture = StateSyncFixtureT<false>;
    // Page-encoded server primary for post-mip8 fork
    using PageServerStateSyncFixture = StateSyncFixtureT<true>;

    template <typename TFixture>
    struct StateSyncTestBothForks : public TFixture
    {
    };

    using StateSyncTestTypes =
        ::testing::Types<StateSyncFixture, PageServerStateSyncFixture>;
    TYPED_TEST_SUITE(StateSyncTestBothForks, StateSyncTestTypes);

    // Trait-aware dispatch wrapper for commit_block
    void commit_block_dispatch(
        monad::Db &primary, monad::Db *const secondary,
        monad_revision const rev, bytes32_t const &block_id,
        BlockHeader const &header, StateDeltas const &deltas,
        BlockCommitAncillaries const &anc)
    {
        SWITCH_MONAD_TRAITS(
            commit_block, primary, secondary, block_id, header, deltas, anc);
        MONAD_ASSERT(false);
    }

    // Commit one block proposal through the production commit_block path, which
    // stamps the canonical state_root (slot pre-mip8, page post-mip8) into the
    // header(s)
    bytes32_t commit_simple_revision_aware(
        monad::Db &primary, monad::Db *const secondary,
        monad_revision const rev, StateDeltas const &deltas, Code const &code,
        BlockHeader const &header, std::vector<Receipt> const &receipts = {},
        std::vector<std::vector<CallFrame>> const &call_frames = {},
        std::vector<Address> const &senders = {},
        std::vector<Transaction> const &txns = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const &withdrawals =
            std::nullopt)
    {
        bytes32_t const block_id =
            header.number ? bytes32_t{header.number} : NULL_HASH_BLAKE3;
        BlockCommitAncillaries const anc{
            .code = code,
            .receipts = receipts,
            .transactions = txns,
            .senders = senders,
            .call_frames = call_frames,
            .ommers = ommers,
            .withdrawals = withdrawals};
        commit_block_dispatch(
            primary, secondary, rev, block_id, header, deltas, anc);
        return block_id;
    }

    // Like commit_simple_revision_aware, then finalize and reposition both
    // timelines (the finalized-block analogue of commit_sequential).
    void commit_sequential_revision_aware(
        monad::Db &primary, monad::Db *const secondary,
        monad_revision const rev, StateDeltas const &deltas, Code const &code,
        BlockHeader const &header, std::vector<Receipt> const &receipts = {},
        std::vector<std::vector<CallFrame>> const &call_frames = {},
        std::vector<Address> const &senders = {},
        std::vector<Transaction> const &txns = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const &withdrawals =
            std::nullopt)
    {
        bytes32_t const block_id = commit_simple_revision_aware(
            primary,
            secondary,
            rev,
            deltas,
            code,
            header,
            receipts,
            call_frames,
            senders,
            txns,
            ommers,
            withdrawals);
        primary.finalize(header.number, block_id);
        primary.set_block_and_prefix(header.number);
        if (secondary != nullptr) {
            secondary->finalize(header.number, block_id);
            secondary->set_block_and_prefix(header.number);
        }
    }

    BlockHeader commit_domain_sequential_revision_aware(
        monad::Db &db, monad_revision const rev,
        DomainStateDeltas const &domain_deltas, StateDeltas const &root_deltas,
        Code const &code, BlockHeader const &header)
    {
        bytes32_t const block_id =
            header.number ? bytes32_t{header.number} : NULL_HASH_BLAKE3;
        auto builder = make_commit_builder(header.number, db);
        builder->add_domain_state_deltas(domain_deltas);
        DomainStateDeltas const *const delta_sets[] = {&domain_deltas};
        db.commit_domain_state_deltas(
            block_id, *builder, delta_sets, header.number, {});

        commit_simple_revision_aware(
            db, nullptr, rev, root_deltas, code, header);
        db.finalize(header.number, block_id);
        db.set_block_and_prefix(header.number);
        return db.read_eth_header();
    }
}

// single timeline server -> slot and page-encoded dual db client
TYPED_TEST(StateSyncTestBothForks, sync_from_latest)
{
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.append = true, .dbname_paths = {this->cdbname}}};
        TrieDb tdb{db};
        // In dual-db set up, both primary and secondary should stay in
        // lockstep.
        {
            auto db2 = db.open_secondary_timeline(
                std::make_unique<MonadOnDiskMachine>());
            MONAD_ASSERT(db2.has_value());
            TrieDb tdb2{*db2};
            ASSERT_TRUE(tdb2.is_page_encoded());
            uint64_t const block_number = N - 257;
            load_header(
                db.load_root_for_version(block_number),
                db,
                BlockHeader{.number = block_number});
            load_header(
                db2->load_root_for_version(block_number),
                *db2,
                BlockHeader{.number = block_number});
            for (size_t i = N - 256; i < N; ++i) {
                BlockHeader const hdr{.parent_hash = parent_hash, .number = i};
                tdb.set_block_and_prefix(i - 1);
                tdb2.set_block_and_prefix(i - 1);
                // Pre-fork (slot canonical): dual-write so both client dbs'
                // headers carry the same slot state_root.
                commit_sequential_revision_aware(
                    tdb,
                    &tdb2,
                    this->get_monad_revision(),
                    StateDeltas({}),
                    {},
                    hdr);
                parent_hash = to_bytes(
                    keccak256(rlp::encode_block_header(tdb.read_eth_header())));
            }
            // Block N: dual-write so both client dbs carry the canonical
            // header
            commit_sequential_revision_aware(
                tdb,
                &tdb2,
                this->get_monad_revision(),
                init_deltas(),
                init_code(),
                BlockHeader{.number = N});
            // a pending proposal at N+1 (not finalized)
            commit_simple_revision_aware(
                tdb,
                &tdb2,
                this->get_monad_revision(),
                StateDeltas({}),
                {},
                BlockHeader{.number = N + 1});
        }
        this->init();
    }
    // Canonical root of the load_db state: slot-encoded pre-mip8, page-encoded
    // post-mip8.
    handle_target(
        this->cctx,
        BlockHeader{
            .parent_hash = parent_hash,
            .state_root =
                this->mip_8_is_active
                    ? 0x3438aff12a8d7d87cfae57d462e250c2dd03b5b06a5fa50a2eb3c8d397877e79_bytes32
                    : 0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32,
            .number = N});
    EXPECT_TRUE(monad_statesync_client_has_reached_target(this->cctx));
    EXPECT_TRUE(monad_statesync_client_finalize(this->cctx));
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
                StateDeltas({}),
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

    mpt::Db cdb{
        std::make_unique<OnDiskMachine>(),
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

TEST(DomainStateRoot, domain_id_metadata_is_root_neutral)
{
    constexpr uint64_t domain = 0x123456789abcdef0ULL;
    Account const acct{.nonce = 1};

    auto const empty_metadata_root =
        domain_root_with_metadata(domain, false, acct);
    auto const encoded_metadata_root =
        domain_root_with_metadata(domain, true, acct);

    EXPECT_NE(empty_metadata_root, NULL_ROOT);
    EXPECT_EQ(empty_metadata_root, encoded_metadata_root);
}

TEST(DomainStateRoot, domain_id_metadata_preserves_account_root)
{
    constexpr uint64_t domain = 0x123456789abcdef0ULL;

    auto const original_root =
        domain_root_with_metadata(domain, true, Account{.balance = 1});
    auto const updated_root =
        domain_root_with_metadata(domain, true, Account{.balance = 2});

    EXPECT_NE(original_root, updated_root);
}

TYPED_TEST(StateSyncTestBothForks, sync_domain_from_empty)
{
    auto const rev = this->get_monad_revision();
    this->init();
    commit_sequential_revision_aware(
        this->sctx,
        nullptr,
        rev,
        StateDeltas{},
        Code{},
        BlockHeader{.number = 0, .timestamp = this->revision_config.timestamp});
    auto const parent_hash = header_hash(this->stdb.read_eth_header());

    constexpr uint64_t domain{0x0102030405060708ULL};
    Address const addr{0x42};
    bytes32_t const key1{0x00};
    bytes32_t const key2{0x01};
    bytes32_t const key3{0x80};
    bytes32_t const value1{0x5678};
    bytes32_t const value2{0x6789};
    bytes32_t const value3{0x789a};
    Account const account{.balance = 100};
    ASSERT_EQ(compute_page_key(key1), compute_page_key(key2));
    ASSERT_NE(compute_page_key(key1), compute_page_key(key3));

    auto hdr = commit_domain_sequential_revision_aware(
        this->sctx,
        rev,
        one_domain_delta(
            domain,
            addr,
            std::nullopt,
            account,
            StorageDeltas{
                {key1, StorageDelta{bytes32_t{}, value1}},
                {key2, StorageDelta{bytes32_t{}, value2}},
                {key3, StorageDelta{bytes32_t{}, value3}}}),
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 1,
            .timestamp = this->revision_config.timestamp});

    handle_target(this->cctx, hdr);
    this->run();
    EXPECT_TRUE(monad_statesync_client_finalize(this->cctx));
    this->set_client_block(1);

    for (TrieDb *const tdb :
         {&this->cctx->tdb, this->cctx->secondary_tdb.get()}) {
        auto const synced_account = tdb->read_account(addr, domain);
        ASSERT_TRUE(synced_account.has_value());
        EXPECT_EQ(synced_account->balance, account.balance);
        EXPECT_EQ(
            tdb->read_storage(addr, synced_account->incarnation, key1, domain),
            value1);
        EXPECT_EQ(
            tdb->read_storage(addr, synced_account->incarnation, key2, domain),
            value2);
        EXPECT_EQ(
            tdb->read_storage(addr, synced_account->incarnation, key3, domain),
            value3);
    }
    expect_domain_id_metadata(this->cctx->db, 1, domain);
    expect_domain_id_metadata(*this->cctx->secondary_db, 1, domain);
    EXPECT_EQ(
        this->stdb.domain_state_root(domain),
        this->canonical_client_tdb().domain_state_root(domain));
}

TYPED_TEST(StateSyncTestBothForks, sync_domain_incremental_update_and_delete)
{
    auto const rev = this->get_monad_revision();
    this->init();
    commit_sequential_revision_aware(
        this->sctx,
        nullptr,
        rev,
        StateDeltas{},
        Code{},
        BlockHeader{.number = 0, .timestamp = this->revision_config.timestamp});
    auto parent_hash = header_hash(this->stdb.read_eth_header());

    constexpr uint64_t domain{0x1111222233334444ULL};
    Address const addr{0x43};
    bytes32_t const key1{0x00};
    bytes32_t const key2{0x01};
    bytes32_t const key3{0x80};
    bytes32_t const value1{0xaaaa};
    bytes32_t const value2{0xbbbb};
    bytes32_t const value3{0xcccc};
    Account const account{.balance = 100};
    ASSERT_EQ(compute_page_key(key1), compute_page_key(key2));
    ASSERT_NE(compute_page_key(key1), compute_page_key(key3));

    auto hdr1 = commit_domain_sequential_revision_aware(
        this->sctx,
        rev,
        one_domain_delta(
            domain,
            addr,
            std::nullopt,
            account,
            StorageDeltas{
                {key1, StorageDelta{bytes32_t{}, value1}},
                {key2, StorageDelta{bytes32_t{}, value2}},
                {key3, StorageDelta{bytes32_t{}, value3}}}),
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 1,
            .timestamp = this->revision_config.timestamp});

    handle_target(this->cctx, hdr1);
    this->run();
    ASSERT_TRUE(monad_statesync_client_finalize(this->cctx));
    this->restart_client();

    parent_hash = header_hash(hdr1);
    auto updated_account = account;
    updated_account.balance = 200;
    auto hdr2 = commit_domain_sequential_revision_aware(
        this->sctx,
        rev,
        one_domain_delta(
            domain,
            addr,
            account,
            updated_account,
            StorageDeltas{{key1, StorageDelta{value1, bytes32_t{}}}}),
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 2,
            .timestamp = this->revision_config.timestamp});

    handle_target(this->cctx, hdr2);
    this->run();
    EXPECT_TRUE(monad_statesync_client_finalize(this->cctx));
    this->set_client_block(2);

    for (TrieDb *const tdb :
         {&this->cctx->tdb, this->cctx->secondary_tdb.get()}) {
        auto const synced_account = tdb->read_account(addr, domain);
        ASSERT_TRUE(synced_account.has_value());
        EXPECT_EQ(synced_account->balance, updated_account.balance);
        EXPECT_EQ(
            tdb->read_storage(addr, synced_account->incarnation, key1, domain),
            bytes32_t{});
        EXPECT_EQ(
            tdb->read_storage(addr, synced_account->incarnation, key2, domain),
            value2);
        EXPECT_EQ(
            tdb->read_storage(addr, synced_account->incarnation, key3, domain),
            value3);
    }
    expect_domain_id_metadata(this->cctx->db, 2, domain);
    expect_domain_id_metadata(*this->cctx->secondary_db, 2, domain);
    EXPECT_EQ(
        this->stdb.domain_state_root(domain),
        this->canonical_client_tdb().domain_state_root(domain));
}

TYPED_TEST(
    StateSyncTestBothForks, sync_multiple_domains_root_isolation_and_code)
{
    auto const rev = this->get_monad_revision();
    this->init();
    commit_sequential_revision_aware(
        this->sctx,
        nullptr,
        rev,
        StateDeltas{},
        Code{},
        BlockHeader{.number = 0, .timestamp = this->revision_config.timestamp});
    auto const parent_hash = header_hash(this->stdb.read_eth_header());

    constexpr uint64_t domain1{0x0102030405060708ULL};
    constexpr uint64_t domain2{0xfedcba9876543210ULL};
    Address const addr{0x44};
    bytes32_t const key{0x01};
    bytes32_t const root_value{0x1111};
    bytes32_t const domain1_value{0x2222};
    bytes32_t const domain2_value{0x3333};
    auto const code_bytes = from_hex("600160005500").value();
    auto const code_hash = to_bytes(keccak256(code_bytes));

    Account const root_account{.balance = 11};
    Account const domain1_account{
        .balance = 22, .code_hash = code_hash, .nonce = 1};
    Account const domain2_account{.balance = 33};

    DomainStateDeltas domain_deltas;
    add_domain_delta(
        domain_deltas,
        domain1,
        addr,
        std::nullopt,
        domain1_account,
        StorageDeltas{{key, StorageDelta{bytes32_t{}, domain1_value}}});
    add_domain_delta(
        domain_deltas,
        domain2,
        addr,
        std::nullopt,
        domain2_account,
        StorageDeltas{{key, StorageDelta{bytes32_t{}, domain2_value}}});

    StateDeltas root_deltas{
        {addr,
         StateDelta{
             .account = {std::nullopt, root_account},
             .storage = {{key, StorageDelta{bytes32_t{}, root_value}}}}}};
    Code code;
    code.emplace(code_hash, vm::make_shared_intercode(code_bytes));

    auto const hdr = commit_domain_sequential_revision_aware(
        this->sctx,
        rev,
        domain_deltas,
        root_deltas,
        code,
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 1,
            .timestamp = this->revision_config.timestamp});

    handle_target(this->cctx, hdr);
    this->run();
    ASSERT_TRUE(monad_statesync_client_finalize(this->cctx));
    this->set_client_block(1);

    for (TrieDb *const tdb :
         {&this->cctx->tdb, this->cctx->secondary_tdb.get()}) {
        auto const actual_root = tdb->read_account(addr);
        auto const actual_domain1 = tdb->read_account(addr, domain1);
        auto const actual_domain2 = tdb->read_account(addr, domain2);
        ASSERT_TRUE(actual_root.has_value());
        ASSERT_TRUE(actual_domain1.has_value());
        ASSERT_TRUE(actual_domain2.has_value());
        EXPECT_EQ(actual_root->balance, root_account.balance);
        EXPECT_EQ(actual_domain1->balance, domain1_account.balance);
        EXPECT_EQ(actual_domain2->balance, domain2_account.balance);
        EXPECT_EQ(
            tdb->read_storage(addr, actual_root->incarnation, key), root_value);
        EXPECT_EQ(
            tdb->read_storage(addr, actual_domain1->incarnation, key, domain1),
            domain1_value);
        EXPECT_EQ(
            tdb->read_storage(addr, actual_domain2->incarnation, key, domain2),
            domain2_value);
        auto const actual_code = tdb->read_code(code_hash);
        ASSERT_TRUE(actual_code);
        EXPECT_EQ(
            byte_string_view(actual_code->code(), actual_code->size()),
            code_bytes);
    }
    EXPECT_EQ(
        this->stdb.domain_state_root(domain1),
        this->canonical_client_tdb().domain_state_root(domain1));
    EXPECT_EQ(
        this->stdb.domain_state_root(domain2),
        this->canonical_client_tdb().domain_state_root(domain2));
}

TYPED_TEST(
    StateSyncTestBothForks, sync_domain_account_delete_preserves_other_domain)
{
    auto const rev = this->get_monad_revision();
    this->init();
    commit_sequential_revision_aware(
        this->sctx,
        nullptr,
        rev,
        StateDeltas{},
        Code{},
        BlockHeader{.number = 0, .timestamp = this->revision_config.timestamp});
    auto parent_hash = header_hash(this->stdb.read_eth_header());

    constexpr uint64_t deleted_domain{0x1111222233334444ULL};
    constexpr uint64_t preserved_domain{0xaaaabbbbccccddddULL};
    Address const addr{0x45};
    bytes32_t const key{0x01};
    bytes32_t const deleted_value{0xaaaa};
    bytes32_t const preserved_value{0xbbbb};
    Account const deleted_account{.balance = 100};
    Account const preserved_account{.balance = 200};

    DomainStateDeltas initial_deltas;
    add_domain_delta(
        initial_deltas,
        deleted_domain,
        addr,
        std::nullopt,
        deleted_account,
        StorageDeltas{{key, StorageDelta{bytes32_t{}, deleted_value}}});
    add_domain_delta(
        initial_deltas,
        preserved_domain,
        addr,
        std::nullopt,
        preserved_account,
        StorageDeltas{{key, StorageDelta{bytes32_t{}, preserved_value}}});
    auto const hdr1 = commit_domain_sequential_revision_aware(
        this->sctx,
        rev,
        initial_deltas,
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 1,
            .timestamp = this->revision_config.timestamp});

    handle_target(this->cctx, hdr1);
    this->run();
    ASSERT_TRUE(monad_statesync_client_finalize(this->cctx));
    this->restart_client();

    parent_hash = header_hash(hdr1);
    auto const hdr2 = commit_domain_sequential_revision_aware(
        this->sctx,
        rev,
        one_domain_delta(deleted_domain, addr, deleted_account, std::nullopt),
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 2,
            .timestamp = this->revision_config.timestamp});

    handle_target(this->cctx, hdr2);
    this->run();
    ASSERT_TRUE(monad_statesync_client_finalize(this->cctx));
    this->set_client_block(2);

    for (TrieDb *const tdb :
         {&this->cctx->tdb, this->cctx->secondary_tdb.get()}) {
        EXPECT_FALSE(tdb->read_account(addr, deleted_domain).has_value());
        auto const preserved = tdb->read_account(addr, preserved_domain);
        ASSERT_TRUE(preserved.has_value());
        EXPECT_EQ(preserved->balance, preserved_account.balance);
        EXPECT_EQ(
            tdb->read_storage(
                addr, preserved->incarnation, key, preserved_domain),
            preserved_value);
    }
    EXPECT_EQ(
        this->stdb.domain_state_root(deleted_domain),
        this->canonical_client_tdb().domain_state_root(deleted_domain));
    EXPECT_EQ(
        this->stdb.domain_state_root(preserved_domain),
        this->canonical_client_tdb().domain_state_root(preserved_domain));
}

TYPED_TEST(StateSyncTestBothForks, domain_storage_before_account_is_buffered)
{
    auto const rev = this->get_monad_revision();
    this->init();
    this->net.defer_first_account_until_storage = true;
    commit_sequential_revision_aware(
        this->sctx,
        nullptr,
        rev,
        StateDeltas{},
        Code{},
        BlockHeader{.number = 0, .timestamp = this->revision_config.timestamp});
    auto const parent_hash = header_hash(this->stdb.read_eth_header());

    constexpr uint64_t domain{0x123456789abcdef0ULL};
    Address const addr{0x46};
    bytes32_t const key{0x01};
    bytes32_t const value{0x9999};
    Account const account{.balance = 100};
    auto const hdr = commit_domain_sequential_revision_aware(
        this->sctx,
        rev,
        one_domain_delta(
            domain,
            addr,
            std::nullopt,
            account,
            StorageDeltas{{key, StorageDelta{bytes32_t{}, value}}}),
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 1,
            .timestamp = this->revision_config.timestamp});

    handle_target(this->cctx, hdr);
    this->run();
    ASSERT_TRUE(this->net.deferred_account.empty());
    ASSERT_TRUE(monad_statesync_client_finalize(this->cctx));
    this->set_client_block(1);
    for (TrieDb *const tdb :
         {&this->cctx->tdb, this->cctx->secondary_tdb.get()}) {
        auto const actual = tdb->read_account(addr, domain);
        ASSERT_TRUE(actual.has_value());
        EXPECT_EQ(
            tdb->read_storage(addr, actual->incarnation, key, domain), value);
    }
}

TEST_F(StateSyncFixture, domain_storage_without_account_fails_finalize)
{
    auto const rev = get_monad_revision();
    init();
    net.drop_first_account = true;
    commit_sequential_revision_aware(
        sctx,
        nullptr,
        rev,
        StateDeltas{},
        Code{},
        BlockHeader{.number = 0, .timestamp = revision_config.timestamp});
    auto const parent_hash = header_hash(stdb.read_eth_header());

    constexpr uint64_t domain{0x123456789abcdef0ULL};
    Address const addr{0x47};
    bytes32_t const key{0x01};
    auto const hdr = commit_domain_sequential_revision_aware(
        sctx,
        rev,
        one_domain_delta(
            domain,
            addr,
            std::nullopt,
            Account{.balance = 100},
            StorageDeltas{{key, StorageDelta{bytes32_t{}, bytes32_t{1}}}}),
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 1,
            .timestamp = revision_config.timestamp});

    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(net.account_was_dropped);
    EXPECT_TRUE(monad_statesync_client_has_reached_target(cctx));
    EXPECT_FALSE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, malformed_domain_upsert_aborts_sync_session)
{
    auto const rev = get_monad_revision();
    init();
    net.corrupt_first_account_domain_suffix = true;
    commit_sequential_revision_aware(
        sctx,
        nullptr,
        rev,
        StateDeltas{},
        Code{},
        BlockHeader{.number = 0, .timestamp = revision_config.timestamp});
    auto const parent_hash = header_hash(stdb.read_eth_header());

    constexpr uint64_t domain{0x123456789abcdef0ULL};
    auto const hdr = commit_domain_sequential_revision_aware(
        sctx,
        rev,
        one_domain_delta(
            domain, Address{0x48}, std::nullopt, Account{.balance = 100}),
        StateDeltas{},
        Code{},
        BlockHeader{
            .parent_hash = parent_hash,
            .number = 1,
            .timestamp = revision_config.timestamp});

    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(net.upsert_was_rejected);
    EXPECT_FALSE(client.success);
    EXPECT_FALSE(monad_statesync_client_has_reached_target(cctx));
}

// single timeline server -> slot and page-encoded dual db client
TYPED_TEST(StateSyncTestBothForks, sync_from_some)
{
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.append = true, .dbname_paths = {this->cdbname}}};
        TrieDb tdb{db};
        auto db2_opt =
            db.open_secondary_timeline(std::make_unique<MonadOnDiskMachine>());
        MONAD_ASSERT(db2_opt.has_value());
        TrieDb tdb2{db2_opt.value()};
        ASSERT_TRUE(tdb2.is_page_encoded());
        load_genesis_state(GENESIS_STATE, tdb);
        load_genesis_state(GENESIS_STATE, tdb2);
        // commit some proposal to client db
        commit_simple(
            tdb,
            StateDeltas({}),
            {},
            NULL_HASH_BLAKE3,
            BlockHeader{.number = 1});
        commit_simple(
            tdb2,
            StateDeltas({}),
            {},
            NULL_HASH_BLAKE3,
            BlockHeader{.number = 1});
        EXPECT_TRUE(db2_opt->load_root_for_version(0) != nullptr);
        load_genesis_state(GENESIS_STATE, this->stdb);
        this->init();
    }

    ASSERT_TRUE(this->stdb.get_root() != nullptr);
    auto const res = this->sdb.find(
        this->stdb.get_root(), concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE), 0);
    ASSERT_TRUE(res.has_value() && res.value().is_valid());
    // Commit a server block, then capture its committed header. The committed
    // state_root is slot pre-mip8 / page post-mip8.
    bytes32_t parent_hash = to_bytes(keccak256(res.value().node->value()));
    auto const commit_server_block_update_parent_hash =
        [&](StateDeltas const &deltas,
            Code const &code,
            uint64_t const number) {
            commit_sequential_revision_aware(
                this->sctx,
                nullptr,
                this->get_monad_revision(),
                deltas,
                code,
                BlockHeader{.parent_hash = parent_hash, .number = number});
            BlockHeader const committed = this->stdb.read_eth_header();
            parent_hash =
                to_bytes(keccak256(rlp::encode_block_header(committed)));
            return committed;
        };

    // existing accounts in genesis
    constexpr auto ADDR1 = 0x000d836201318ec6899a67540690382780743280_address;
    constexpr auto ADDR2 = 0x02d4a30968a39e2b3498c3a6a4ed45c1c6646822_address;
    // new account address
    constexpr auto ADDR3 = 0x5353535353535353535353535353535353535353_address;

    // delete existing account ADDR1
    auto const acct1 = this->stdb.read_account(ADDR1);
    MONAD_ASSERT(acct1.has_value());
    auto const hdr1 = commit_server_block_update_parent_hash(
        StateDeltas({{ADDR1, {.account = {acct1, std::nullopt}}}}), Code{}, 1);

    // new storage to existing account ADDR2
    auto acct2 = this->stdb.read_account(ADDR2);
    auto const hdr2 = commit_server_block_update_parent_hash(
        StateDeltas(
            {{ADDR2,
              {.account = {acct2, acct2},
               .storage =
                   {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                     {{},
                      0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}}),
        Code{},
        2);

    // add new smart contract ADDR3
    auto const code =
        from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                 "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                 "ffffffffffffffffffffff0160005500")
            .value();
    auto const code_hash = to_bytes(keccak256(code));
    auto const icode = vm::make_shared_intercode(code);
    auto const hdr3 = commit_server_block_update_parent_hash(
        StateDeltas(
            {{ADDR3,
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
                      0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}}),
        Code{{code_hash, icode}},
        3);

    // delete storage in account ADDR2
    acct2 = this->stdb.read_account(ADDR2);
    auto const hdr4 = commit_server_block_update_parent_hash(
        StateDeltas(
            {{ADDR2,
              {.account = {acct2, acct2},
               .storage =
                   {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                     {0x0000000000000013370000000000000000000000000000000000000000000003_bytes32,
                      {}}}}}}}),
        Code{},
        4);

    // account incarnation for ADDR2
    auto const old = this->stdb.read_account(ADDR2);
    acct2 = old;
    acct2->incarnation = Incarnation{5, 0};
    auto const hdr5 = commit_server_block_update_parent_hash(
        StateDeltas(
            {{ADDR2,
              {.account = {old, acct2},
               .storage =
                   {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                     {{},
                      0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}}),
        Code{},
        5);

    // delete smart contract at ADDR3
    auto const acct3 = this->stdb.read_account(ADDR3);
    MONAD_ASSERT(acct3.has_value());
    auto const hdr6 = commit_server_block_update_parent_hash(
        StateDeltas({{ADDR3, {.account = {acct3, std::nullopt}}}}), Code{}, 6);

    handle_target(this->cctx, hdr1);
    this->run();

    handle_target(this->cctx, hdr2);
    this->run();

    handle_target(this->cctx, hdr3);
    this->run();

    handle_target(this->cctx, hdr4);
    this->run();

    handle_target(this->cctx, hdr5);
    this->run();

    handle_target(this->cctx, hdr6);
    this->run();

    EXPECT_TRUE(monad_statesync_client_finalize(this->cctx));

    // find transaction trie
    mpt::RODb cdb{ReadOnlyOnDiskDbConfig{.dbname_paths = {this->cdbname}}};
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

TYPED_TEST(StateSyncTestBothForks, deletion_proposal)
{
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.append = true, .dbname_paths = {this->cdbname}}};
        TrieDb tdb{db};
        auto db2_opt =
            db.open_secondary_timeline(std::make_unique<MonadOnDiskMachine>());
        MONAD_ASSERT(db2_opt.has_value());
        TrieDb tdb2{db2_opt.value()};
        ASSERT_TRUE(tdb2.is_page_encoded());
        load_genesis_state(GENESIS_STATE, tdb);
        load_genesis_state(GENESIS_STATE, tdb2);

        load_genesis_state(GENESIS_STATE, this->stdb);
        this->init();
    }
    ASSERT_TRUE(this->stdb.get_root() != nullptr);
    auto const res = this->sdb.find(
        this->stdb.get_root(), concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE), 0);
    ASSERT_TRUE(res.has_value() && res.value().is_valid());
    // delete ADDR1 on one fork
    {
        constexpr auto ADDR1 =
            0x000d836201318ec6899a67540690382780743280_address;
        auto const acct = this->sctx.read_account(ADDR1);
        ASSERT_TRUE(acct.has_value());
        StateDeltas deltas{{ADDR1, {.account = {acct, std::nullopt}}}};
        this->sctx.set_block_and_prefix(0);
        commit_simple(
            this->sctx,
            StateDeltas(std::move(deltas)),
            Code{},
            bytes32_t{1},
            BlockHeader{.number = 1});
    }
    // delete ADDR2 on another
    {
        constexpr auto ADDR2 =
            0x001762430ea9c3a26e5749afdb70da5f78ddbb8c_address;
        auto const acct = this->sctx.read_account(ADDR2);
        ASSERT_TRUE(acct.has_value());
        StateDeltas deltas{{ADDR2, {.account = {acct, std::nullopt}}}};
        this->sctx.set_block_and_prefix(0);
        commit_simple(
            this->sctx,
            StateDeltas(std::move(deltas)),
            Code{},
            bytes32_t{2},
            BlockHeader{.number = 1});
    }
    this->sctx.finalize(1, bytes32_t{2});

    this->sctx.set_block_and_prefix(1, bytes32_t{1});
    auto const bad_header = this->sctx.read_eth_header();

    this->sctx.set_block_and_prefix(1, bytes32_t{2});
    auto const finalized_header = this->sctx.read_eth_header();

    EXPECT_NE(finalized_header.state_root, bad_header.state_root);
    handle_target(this->cctx, finalized_header);
    this->run();

    EXPECT_TRUE(monad_statesync_client_finalize(this->cctx));
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    commit_sequential(
        stdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, Account{.balance = 100}},
                  .storage = {}}}}),
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

// Pre-fork dual-timeline server -> dual-timeline client
TEST_F(StateSyncFixture, pre_fork_dual_timeline_server_to_dual_db_client)
{
    mpt::Db secondary_sdb =
        sdb.activate_secondary_timeline(std::make_unique<MonadOnDiskMachine>());
    TrieDb secondary_stdb{secondary_sdb};
    ASSERT_TRUE(secondary_stdb.is_page_encoded());

    init();
    uint64_t const timestamp = revision_config.timestamp;
    monad_revision const rev = cctx->chain->get_monad_revision(timestamp);

    // ADDR_A holds five slots: three share one page_key, two share another, so
    // the page secondary holds genuine multi-slot pages. The server dual-writes
    // every block to both its slot primary and page secondary via commit_block;
    // the client in turn receives slot-encoded upserts and dual-writes them to
    // its own slot Db1 and page Db2. The test compares the two page tries at
    // the end.
    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    load_header(
        sdb.load_root_for_version(N - 257),
        sdb,
        BlockHeader{.number = N - 257});
    load_header(
        secondary_sdb.load_root_for_version(N - 257),
        secondary_sdb,
        BlockHeader{.number = N - 257});
    for (size_t i = N - 256; i < N; ++i) {
        stdb.set_block_and_prefix(i - 1);
        secondary_stdb.set_block_and_prefix(i - 1);
        commit_sequential_revision_aware(
            stdb,
            &secondary_stdb,
            rev,
            {},
            Code{},
            BlockHeader{
                .parent_hash = parent_hash,
                .number = i,
                .timestamp = timestamp});
        EXPECT_EQ(
            stdb.read_eth_header().state_root,
            secondary_stdb.read_eth_header().state_root);
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }

    // Slots 0x00, 0x01, 0x7f all map to page_key 0 (low 7 bits are offset).
    // Slots 0x80, 0x81 map to page_key 1.
    constexpr auto slot_a = bytes32_t{uint64_t{0x00}};
    constexpr auto slot_b = bytes32_t{uint64_t{0x01}};
    constexpr auto slot_c = bytes32_t{uint64_t{0x7f}};
    constexpr auto slot_d = bytes32_t{uint64_t{0x80}};
    constexpr auto slot_e = bytes32_t{uint64_t{0x81}};
    constexpr auto val_a =
        0x00000000000000000000000000000000000000000000000000000000000000aa_bytes32;
    constexpr auto val_b =
        0x00000000000000000000000000000000000000000000000000000000000000bb_bytes32;
    constexpr auto val_c =
        0x00000000000000000000000000000000000000000000000000000000000000cc_bytes32;
    constexpr auto val_d =
        0x00000000000000000000000000000000000000000000000000000000000000dd_bytes32;
    constexpr auto val_e =
        0x00000000000000000000000000000000000000000000000000000000000000ee_bytes32;

    ASSERT_EQ(compute_page_key(slot_a), compute_page_key(slot_b));
    ASSERT_EQ(compute_page_key(slot_a), compute_page_key(slot_c));
    ASSERT_EQ(compute_page_key(slot_d), compute_page_key(slot_e));
    ASSERT_NE(compute_page_key(slot_a), compute_page_key(slot_d));

    StateDeltas const storage_deltas{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, Account{.balance = 100}},
             .storage = {
                 {slot_a, {bytes32_t{}, val_a}},
                 {slot_b, {bytes32_t{}, val_b}},
                 {slot_c, {bytes32_t{}, val_c}},
                 {slot_d, {bytes32_t{}, val_d}},
                 {slot_e, {bytes32_t{}, val_e}}}}}};

    // Dual-write the state block to both timelines
    commit_sequential_revision_aware(
        stdb,
        &secondary_stdb,
        rev,
        storage_deltas,
        Code{},
        BlockHeader{.number = N, .timestamp = timestamp});

    handle_target(
        cctx,
        BlockHeader{
            .parent_hash = parent_hash,
            .state_root = stdb.read_eth_header().state_root,
            .number = N,
            .timestamp = timestamp});
    run();

    EXPECT_TRUE(monad_statesync_client_finalize(cctx));

    // both timelines db state root should match
    cctx->tdb.set_block_and_prefix(N);
    stdb.set_block_and_prefix(N);
    EXPECT_EQ(stdb.state_root(), cctx->tdb.state_root());

    cctx->secondary_tdb->set_block_and_prefix(N);
    secondary_stdb.set_block_and_prefix(N);
    EXPECT_EQ(secondary_stdb.state_root(), cctx->secondary_tdb->state_root());
}

TEST_F(
    PageServerStateSyncFixture, post_fork_sync_page_primary_to_dual_db_client)
{
    ASSERT_TRUE(this->stdb.is_page_encoded());

    this->init();
    uint64_t const timestamp = this->revision_config.timestamp;
    monad_revision const rev = this->cctx->chain->get_monad_revision(timestamp);
    ASSERT_TRUE(mip_8_active(rev));

    // ADDR_A holds five slots: 0x00/0x01/0x7f share one page, 0x80/0x81 a
    // second page, so the server holds genuine multi-slot pages to expand.
    constexpr auto slot_a = bytes32_t{uint64_t{0x00}};
    constexpr auto slot_b = bytes32_t{uint64_t{0x01}};
    constexpr auto slot_c = bytes32_t{uint64_t{0x7f}};
    constexpr auto slot_d = bytes32_t{uint64_t{0x80}};
    constexpr auto slot_e = bytes32_t{uint64_t{0x81}};
    constexpr auto val_a =
        0x00000000000000000000000000000000000000000000000000000000000000aa_bytes32;
    constexpr auto val_b =
        0x00000000000000000000000000000000000000000000000000000000000000bb_bytes32;
    constexpr auto val_c =
        0x00000000000000000000000000000000000000000000000000000000000000cc_bytes32;
    constexpr auto val_d =
        0x00000000000000000000000000000000000000000000000000000000000000dd_bytes32;
    constexpr auto val_e =
        0x00000000000000000000000000000000000000000000000000000000000000ee_bytes32;

    ASSERT_EQ(compute_page_key(slot_a), compute_page_key(slot_b));
    ASSERT_EQ(compute_page_key(slot_a), compute_page_key(slot_c));
    ASSERT_EQ(compute_page_key(slot_d), compute_page_key(slot_e));
    ASSERT_NE(compute_page_key(slot_a), compute_page_key(slot_d));

    constexpr auto N = 1'000'000;
    bytes32_t parent_hash{NULL_HASH};
    load_header(
        sdb.load_root_for_version(N - 257),
        sdb,
        BlockHeader{.number = N - 257});
    for (size_t i = N - 256; i < N; ++i) {
        stdb.set_block_and_prefix(i - 1);
        commit_sequential_revision_aware(
            stdb,
            nullptr,
            rev,
            {},
            Code{},
            BlockHeader{
                .parent_hash = parent_hash,
                .number = i,
                .timestamp = timestamp});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }

    StateDeltas const storage_deltas{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, Account{.balance = 100}},
             .storage = {
                 {slot_a, {bytes32_t{}, val_a}},
                 {slot_b, {bytes32_t{}, val_b}},
                 {slot_c, {bytes32_t{}, val_c}},
                 {slot_d, {bytes32_t{}, val_d}},
                 {slot_e, {bytes32_t{}, val_e}}}}}};

    commit_sequential_revision_aware(
        stdb,
        nullptr,
        rev,
        storage_deltas,
        Code{},
        BlockHeader{.number = N, .timestamp = timestamp});

    handle_target(
        cctx,
        BlockHeader{
            .parent_hash = parent_hash,
            .state_root = stdb.state_root(),
            .number = N,
            .timestamp = timestamp});
    run();

    EXPECT_TRUE(monad_statesync_client_finalize(cctx));

    // Post-fork the client's page secondary must match the page-encoded server
    // primary.
    stdb.set_block_and_prefix(N);
    cctx->secondary_tdb->set_block_and_prefix(N);
    EXPECT_EQ(stdb.state_root(), cctx->secondary_tdb->state_root());
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    commit_sequential(
        stdb, StateDeltas({}), Code{}, BlockHeader{.number = 1'000'000});
    init();
    handle_target(cctx, BlockHeader{.parent_hash = parent_hash, .number = N});
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, sync_client_has_proposals)
{
    {
        // init client DB
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            OnDiskDbConfig{.append = true, .dbname_paths = {cdbname}}};
        TrieDb tdb{db};
        tdb.reset_root(load_header({}, db, BlockHeader{.number = 0}), 0);
        for (uint64_t n = 1; n <= 249; ++n) {
            commit_simple(
                tdb,
                StateDeltas({}),
                {},
                bytes32_t{n},
                BlockHeader{.number = n});
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
            commit_sequential(stdb, StateDeltas({}), {}, hdr);
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
        commit_sequential(stdb, StateDeltas({}), {}, hdr);
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    BlockHeader hdr{.parent_hash = parent_hash, .number = 100};
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, Account{.balance = 100}},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {bytes32_t{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}}),
        Code{},
        hdr);
    parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr = BlockHeader{.parent_hash = parent_hash, .number = 101};
    commit_sequential(sctx, StateDeltas({}), {}, hdr);
    parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr = BlockHeader{.parent_hash = parent_hash, .number = 102};
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {Account{.balance = 100}, Account{.balance = 200}},
                  .storage = {}}}}),
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
        commit_sequential(stdb, StateDeltas({}), {}, hdr);
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }
    BlockHeader hdr{.parent_hash = parent_hash, .number = 100};
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, Account{.balance = 100}},
                  .storage =
                      {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                        {bytes32_t{},
                         0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}}),
        Code{},
        hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr.number = 101;
    commit_sequential(sctx, StateDeltas({}), {}, hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    hdr.number = 102;
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {Account{.balance = 100}, std::nullopt},
                  .storage = {}}}}),
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
    commit_sequential(sctx, StateDeltas({}), Code{}, hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 1;
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, Account{.balance = 100}},
                  .storage = {}}}}),
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
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {Account{.balance = 100}, std::nullopt},
                  .storage = {}}}}),
        Code{},
        hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    client.rqs.clear();

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 3;
    hdr.state_root = NULL_ROOT;
    commit_sequential(sctx, StateDeltas({}), Code{}, hdr);
    EXPECT_EQ(sctx.state_root(), hdr.state_root);
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
}

TEST_F(StateSyncFixture, delete_updated_account)
{
    init();
    BlockHeader hdr{.parent_hash = NULL_HASH};
    commit_sequential(sctx, StateDeltas({}), Code{}, hdr);

    Account const a{.balance = 100, .incarnation = Incarnation{1, 0}};

    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    hdr.number = 1;
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{.account = {std::nullopt, a}, .storage = {}}}}),
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
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {a, a},
                  .storage = {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}}}}}}),
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
        StateDeltas(
            {{ADDR_A,
              StateDelta{.account = {a, std::nullopt}, .storage = {}}}}),
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
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
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, a},
                  .storage =
                      {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}},
                       {bytes32_t{1}, {bytes32_t{}, bytes32_t{64}}}}}}}),
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
        StateDeltas(
            {{ADDR_A,
              StateDelta{.account = {a, std::nullopt}, .storage = {}}}}),
        Code{},
        hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.number = 1'000'002;
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, a},
                  .storage = {{bytes32_t{}, {bytes32_t{}, bytes32_t{64}}}}}}}),
        Code{},
        hdr);
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    hdr.state_root =
        0x7537c605448f37499129a14743eb442cd09e5b2ec50ef7e73a5e715ee82d0453_bytes32;
    hdr.number = 1'000'003;
    commit_sequential(
        sctx,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {a, a},
                  .storage = {{bytes32_t{}, {bytes32_t{64}, bytes32_t{}}}}}}}),
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
    commit_sequential(sctx, StateDeltas({}), Code{}, hdr);

    constexpr auto ADDR1 = 0x5353535353535353535353535353535353535353_address;
    hdr.parent_hash =
        to_bytes(keccak256(rlp::encode_block_header(stdb.read_eth_header())));

    auto const code =
        from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
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
        StateDeltas(
            {{ADDR1,
              {.account = {std::nullopt, a},
               .storage =
                   {{0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32,
                     {{},
                      0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}

            }),
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
        StateDeltas(
            {{ADDR1,
              {.account = {a, a},
               .storage =
                   {{0x0000000000000000000000000000000000000000000000000000000011110000_bytes32,
                     {{},
                      0x0000000000000013370000000000000000000000000000000000000000000003_bytes32}}}}}

            }),
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(stdb.read_eth_header())));
    }

    BlockHeader const hdr{
        .parent_hash = parent_hash,
        .state_root =
            0x50510e4f9ecc40a8cc5819bdc589a0e09c172ed268490d5f755dba939f7e8997_bytes32,
        .number = N};
    StateDeltas deltas{v.begin(), v.end()};
    commit_sequential(stdb, StateDeltas(std::move(deltas)), Code{}, hdr);
    init();
    handle_target(cctx, hdr);
    run();
    EXPECT_TRUE(monad_statesync_client_finalize(cctx));
    flush_logger();
}

TEST(StatesyncServerContext, forwards_domain_state_commits)
{
    mpt::Db db{std::make_unique<OnDiskMachine>(), mpt::OnDiskDbConfig{}};
    TrieDb tdb{db};
    tdb.reset_root(load_header({}, db, BlockHeader{.number = 0}), 0);
    auto ctx = std::make_unique<monad_statesync_server_context>(tdb);

    constexpr uint64_t domain{0x0102030405060708ULL};
    Address const addr{0x42};
    Account const account{.balance = 123};

    DomainStateDeltas domain_state;
    DomainStateDeltas::accessor domain_it{};
    domain_state.emplace(domain_it, domain, std::make_unique<StateDeltas>());
    StateDeltas::accessor it{};
    domain_it->second->emplace(
        it,
        addr,
        StateDelta{.account = {std::nullopt, account}, .storage = {}});

    auto builder = make_commit_builder(1, *ctx);
    builder->add_domain_state_deltas(domain_state);
    DomainStateDeltas const *const delta_sets[] = {&domain_state};
    auto const roots = ctx->commit_domain_state_deltas(
        bytes32_t{1}, *builder, delta_sets, 1, {});

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, domain);
    EXPECT_NE(roots[0].second, bytes32_t{});

    auto const actual = ctx->read_account(addr, domain);
    ASSERT_TRUE(actual.has_value());
    EXPECT_EQ(actual->balance, account.balance);
}

TEST(StatesyncServerContext, forwards_empty_domain_state_commit)
{
    mpt::Db db{std::make_unique<OnDiskMachine>(), mpt::OnDiskDbConfig{}};
    TrieDb tdb{db};
    tdb.reset_root(load_header({}, db, BlockHeader{.number = 0}), 0);
    auto ctx = std::make_unique<monad_statesync_server_context>(tdb);

    constexpr uint64_t domain{0x0102030405060708ULL};
    Address const addr{0x42};

    DomainStateDeltas domain_state;
    DomainStateDeltas::accessor domain_it{};
    domain_state.emplace(domain_it, domain, std::make_unique<StateDeltas>());

    auto builder = make_commit_builder(1, *ctx);
    builder->add_domain_state_deltas(domain_state);
    DomainStateDeltas const *const delta_sets[] = {&domain_state};
    auto const roots = ctx->commit_domain_state_deltas(
        bytes32_t{1}, *builder, delta_sets, 1, {});

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, domain);
    EXPECT_EQ(roots[0].second, NULL_ROOT);
    EXPECT_FALSE(ctx->read_account(addr, domain).has_value());
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
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
            stdb,
            StateDeltas({}),
            {},
            BlockHeader{.parent_hash = parent_hash, .number = i});
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

TEST(ProtocolValidation, storage_deletion_rejects_oversized_key)
{
    StatesyncProtocolV1 proto;

    Address a{0xdeadbeef};
    byte_string oversized_key(33, 0xff);

    byte_string buf{};
    buf += to_byte_string_view(a.bytes);
    buf += rlp::encode_string2(oversized_key);

    EXPECT_FALSE(proto.handle_upsert(
        nullptr, SYNC_TYPE_UPSERT_STORAGE_DELETE, buf.data(), buf.size()));
}

TEST(ProtocolValidation, upserts_reject_trailing_bytes)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        Address a{0xdeadbeef};
        Account acct{.balance = 1};
        bytes32_t key{1};
        bytes32_t val{2};

        auto account_buf = encode_account_db(a, acct);
        account_buf.push_back(0xff);
        EXPECT_FALSE(proto.handle_upsert(
            &ctx,
            SYNC_TYPE_UPSERT_ACCOUNT,
            account_buf.data(),
            account_buf.size()));

        byte_string storage_buf{};
        storage_buf += to_byte_string_view(a.bytes);
        storage_buf += encode_storage_db(key, val);
        storage_buf.push_back(0xff);
        EXPECT_FALSE(proto.handle_upsert(
            &ctx,
            SYNC_TYPE_UPSERT_STORAGE,
            storage_buf.data(),
            storage_buf.size()));

        byte_string account_delete_buf{};
        account_delete_buf += to_byte_string_view(a.bytes);
        account_delete_buf.push_back(0xff);
        EXPECT_FALSE(proto.handle_upsert(
            &ctx,
            SYNC_TYPE_UPSERT_ACCOUNT_DELETE,
            account_delete_buf.data(),
            account_delete_buf.size()));

        byte_string storage_delete_buf{};
        storage_delete_buf += to_byte_string_view(a.bytes);
        storage_delete_buf += rlp::encode_bytes32_compact(key);
        storage_delete_buf.push_back(0xff);
        EXPECT_FALSE(proto.handle_upsert(
            &ctx,
            SYNC_TYPE_UPSERT_STORAGE_DELETE,
            storage_delete_buf.data(),
            storage_delete_buf.size()));

        auto header_buf = rlp::encode_block_header(BlockHeader{.number = 1});
        header_buf.push_back(0xff);
        EXPECT_FALSE(proto.handle_upsert(
            &ctx,
            SYNC_TYPE_UPSERT_HEADER,
            header_buf.data(),
            header_buf.size()));
    }
    std::filesystem::remove(dbname);
}

TEST(ProtocolValidation, account_upsert_accepts_domain_suffix)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        Address a{0xdeadbeef};
        Account acct{.balance = 1};

        byte_string buf = encode_account_db(a, acct);
        buf += rlp::encode_unsigned(uint64_t{1});

        EXPECT_TRUE(proto.handle_upsert(
            &ctx, SYNC_TYPE_UPSERT_ACCOUNT, buf.data(), buf.size()));
    }
    std::filesystem::remove(dbname);
}

TEST(ProtocolValidation, account_upsert_rejects_zero_domain_suffix)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        Address a{0xdeadbeef};
        Account acct{.balance = 1};

        byte_string buf = encode_account_db(a, acct);
        buf += rlp::encode_unsigned(uint64_t{0});

        EXPECT_FALSE(proto.handle_upsert(
            &ctx, SYNC_TYPE_UPSERT_ACCOUNT, buf.data(), buf.size()));
    }
    std::filesystem::remove(dbname);
}

TEST(ProtocolValidation, storage_upsert_accepts_domain_suffix)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        Address a{0xdeadbeef};
        bytes32_t key{1};
        bytes32_t val{2};

        byte_string buf{};
        buf += to_byte_string_view(a.bytes);
        buf += encode_storage_db(key, val);
        buf += rlp::encode_unsigned(uint64_t{1});

        EXPECT_TRUE(proto.handle_upsert(
            &ctx, SYNC_TYPE_UPSERT_STORAGE, buf.data(), buf.size()));
    }
    std::filesystem::remove(dbname);
}

TEST(ProtocolValidation, storage_upsert_rejects_malformed_domain_suffix)
{
    StatesyncProtocolV1 proto;

    Address a{0xdeadbeef};
    bytes32_t key{1};
    bytes32_t val{2};

    byte_string buf{};
    buf += to_byte_string_view(a.bytes);
    buf += encode_storage_db(key, val);
    buf += rlp::encode_unsigned(uint64_t{1});
    buf += rlp::encode_unsigned(uint64_t{2});

    EXPECT_FALSE(proto.handle_upsert(
        nullptr, SYNC_TYPE_UPSERT_STORAGE, buf.data(), buf.size()));
}

TEST(ProtocolValidation, account_deletion_accepts_domain_suffix)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        Address a{0xdeadbeef};

        byte_string buf{};
        buf += to_byte_string_view(a.bytes);
        buf += rlp::encode_unsigned(uint64_t{1});

        EXPECT_TRUE(proto.handle_upsert(
            &ctx, SYNC_TYPE_UPSERT_ACCOUNT_DELETE, buf.data(), buf.size()));
    }
    std::filesystem::remove(dbname);
}

TEST(ProtocolValidation, storage_deletion_accepts_domain_suffix)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        Address a{0xdeadbeef};
        bytes32_t key{1};

        byte_string buf{};
        buf += to_byte_string_view(a.bytes);
        buf += rlp::encode_bytes32_compact(key);
        buf += rlp::encode_unsigned(uint64_t{1});

        EXPECT_TRUE(proto.handle_upsert(
            &ctx, SYNC_TYPE_UPSERT_STORAGE_DELETE, buf.data(), buf.size()));
    }
    std::filesystem::remove(dbname);
}

TEST(ProtocolValidation, domain_suffix_rejects_zero_and_multiple_items)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        Address const addr{0xdeadbeef};
        Account const account{.balance = 1};
        bytes32_t const key{1};
        bytes32_t const value{2};

        byte_string account_upsert = encode_account_db(addr, account);
        byte_string storage_upsert{};
        storage_upsert += to_byte_string_view(addr.bytes);
        storage_upsert += encode_storage_db(key, value);
        byte_string account_delete{};
        account_delete += to_byte_string_view(addr.bytes);
        byte_string storage_delete{};
        storage_delete += to_byte_string_view(addr.bytes);
        storage_delete += rlp::encode_bytes32_compact(key);

        std::array const messages{
            std::pair{SYNC_TYPE_UPSERT_ACCOUNT, std::move(account_upsert)},
            std::pair{SYNC_TYPE_UPSERT_STORAGE, std::move(storage_upsert)},
            std::pair{
                SYNC_TYPE_UPSERT_ACCOUNT_DELETE, std::move(account_delete)},
            std::pair{
                SYNC_TYPE_UPSERT_STORAGE_DELETE, std::move(storage_delete)}};

        for (auto const &[type, payload] : messages) {
            auto zero_domain = payload;
            zero_domain += rlp::encode_unsigned(uint64_t{0});
            EXPECT_FALSE(proto.handle_upsert(
                &ctx, type, zero_domain.data(), zero_domain.size()));

            auto multiple_domains = payload;
            multiple_domains += rlp::encode_unsigned(uint64_t{1});
            multiple_domains += rlp::encode_unsigned(uint64_t{2});
            EXPECT_FALSE(proto.handle_upsert(
                &ctx, type, multiple_domains.data(), multiple_domains.size()));
        }
    }
    std::filesystem::remove(dbname);
}

TEST(ProtocolValidation, header_upsert_rejects_trailing_bytes)
{
    StatesyncProtocolV1 proto;

    auto const dbname = tmp_dbname();
    {
        monad_statesync_client client;
        monad_statesync_client_context ctx{
            CHAIN_CONFIG_MONAD_TESTNET,
            {dbname},
            std::nullopt,
            4,
            &client,
            &statesync_send_request};

        byte_string buf = rlp::encode_block_header(BlockHeader{.number = 1});
        buf += rlp::encode_unsigned(uint64_t{1});

        EXPECT_FALSE(proto.handle_upsert(
            &ctx, SYNC_TYPE_UPSERT_HEADER, buf.data(), buf.size()));
    }
    std::filesystem::remove(dbname);
}
