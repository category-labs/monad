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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/test/test_fixtures_gtest.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/traverse_util.hpp>
#include <category/mpt/update.hpp>

#include <ethash/keccak.hpp>
#include <intx/intx.hpp>
#include <nlohmann/json.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <algorithm>
#include <bit>
#include <cstdint>
#include <deque>
#include <filesystem>
#include <fstream>
#include <memory>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::test;
using namespace monad::literals;

namespace
{
    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto value1 =
        0x0000000000000013370000000000000000000000000000000000000000000003_bytes32;
    constexpr auto value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;

    struct InMemoryTrieDbFixture : public ::testing::Test
    {
        static constexpr bool on_disk = false;

        mpt::Db db{std::make_unique<InMemoryMachine>()};
        vm::VM vm;
    };

    struct OnDiskTrieDbFixture : public ::testing::Test
    {
        static constexpr bool on_disk = true;

        mpt::Db db{std::make_unique<OnDiskMachine>(), mpt::OnDiskDbConfig{}};
        vm::VM vm;
    };

    using OnDiskTrieDbWithFileFixture =
        OnDiskDbWithFileFixtureBase<OnDiskMachine>;

    ///////////////////////////////////////////
    // DB Getters
    ///////////////////////////////////////////
    std::vector<CallFrame> read_call_frame(
        mpt::Node::SharedPtr const root, mpt::Db &db,
        uint64_t const block_number, uint64_t const txn_idx)
    {
        using namespace mpt;

        using KeyedChunk = std::pair<Nibbles, byte_string>;

        Nibbles const min = mpt::concat(
            FINALIZED_NIBBLE,
            CALL_FRAME_NIBBLE,
            NibblesView{serialize_as_big_endian<sizeof(uint32_t)>(txn_idx)});
        Nibbles const max = mpt::concat(
            FINALIZED_NIBBLE,
            CALL_FRAME_NIBBLE,
            NibblesView{
                serialize_as_big_endian<sizeof(uint32_t)>(txn_idx + 1)});

        std::vector<KeyedChunk> chunks;
        RangedGetMachine machine{
            min,
            max,
            [&chunks](NibblesView const path, byte_string_view const value) {
                chunks.emplace_back(path, value);
            }};
        db.traverse(root, machine, block_number);
        MONAD_ASSERT(!chunks.empty());

        std::sort(
            chunks.begin(),
            chunks.end(),
            [](KeyedChunk const &c, KeyedChunk const &c2) {
                return c.first < NibblesView{c2.first};
            });

        byte_string const call_frames_encoded = std::accumulate(
            std::make_move_iterator(chunks.begin()),
            std::make_move_iterator(chunks.end()),
            byte_string{},
            [](byte_string const acc, KeyedChunk const chunk) {
                return std::move(acc) + std::move(chunk.second);
            });

        byte_string_view view{call_frames_encoded};
        auto const call_frame = rlp::decode_call_frames(view);
        MONAD_ASSERT(!call_frame.has_error());
        MONAD_ASSERT(view.empty());
        return call_frame.value();
    }

    std::pair<bytes32_t, bytes32_t> read_storage_and_slot(
        mpt::Node::SharedPtr const &root, mpt::Db const &db,
        uint64_t const block_number, Address const &addr, bytes32_t const &key)
    {
        auto const find_res = db.find(
            root,
            mpt::concat(
                FINALIZED_NIBBLE,
                STATE_NIBBLE,
                mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
                mpt::NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
            block_number);
        if (!find_res.has_value()) {
            return {};
        }
        auto encoded_storage = find_res.value().node->value();
        auto const storage = decode_storage_db(encoded_storage);
        MONAD_ASSERT(!storage.has_error());
        return storage.value();
    }

    std::vector<Address>
    recover_senders(std::vector<Transaction> const &transactions)
    {
        std::vector<Address> senders;
        senders.reserve(transactions.size());
        for (auto const &tx : transactions) {
            auto const sender = recover_sender(tx);
            MONAD_ASSERT(sender.has_value());
            senders.emplace_back(sender.value());
        }
        return senders;
    }
}

template <typename TDB>
struct DBTest : public TDB
{
};

using DBTypes = ::testing::Types<InMemoryTrieDbFixture, OnDiskTrieDbFixture>;
TYPED_TEST_SUITE(DBTest, DBTypes);

namespace
{
    void seed_finalized_block_zero(mpt::Db &db, TrieDb &tdb)
    {
        tdb.reset_root(load_header({}, db, BlockHeader{.number = 0}), 0);
    }

    mpt::Nibbles
    namespace_path(mpt::NibblesView const prefix, uint64_t const ns)
    {
        uint8_t ns_bytes[sizeof(uint64_t)];
        intx::be::store(ns_bytes, ns);
        return mpt::concat(
            prefix,
            namespace_state_nibbles,
            mpt::NibblesView{to_byte_string_view(ns_bytes)});
    }

    mpt::Nibbles namespace_path(uint64_t const ns)
    {
        return namespace_path(finalized_nibbles, ns);
    }

    mpt::Nibbles namespace_account_path(uint64_t const ns, Address const &addr)
    {
        return mpt::concat(
            namespace_path(ns),
            mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})});
    }

    mpt::Nibbles namespace_storage_path(
        uint64_t const ns, Address const &addr, bytes32_t const &key)
    {
        return mpt::concat(
            namespace_account_path(ns, addr),
            mpt::NibblesView{keccak256({key.bytes, sizeof(key.bytes)})});
    }

    void add_state_delta(
        StateDeltas &state_deltas, Address const &addr, StateDelta delta)
    {
        StateDeltas::accessor it{};
        state_deltas.emplace(it, addr, std::move(delta));
    }

    void add_namespace_state_delta(
        NamespacedStateDeltas &ns_deltas, uint64_t const ns,
        Address const &addr, StateDelta delta)
    {
        NamespacedStateDeltas::accessor ns_it{};
        ns_deltas.emplace(ns_it, ns, StateDeltas{});
        add_state_delta(ns_it->second, addr, std::move(delta));
    }

    bytes32_t commit_plain_state_root(
        TrieDb &tdb, StateDeltas const &state_deltas,
        uint64_t const block_number, bytes32_t const &block_id)
    {
        CommitBuilder builder(block_number);
        builder.add_state_deltas(state_deltas);
        BlockHeader header{.number = block_number};
        tdb.commit(
            block_id, builder, header, state_deltas, [&](BlockHeader &h) {
                h.state_root = tdb.state_root();
            });
        return tdb.state_root();
    }

    NamespaceStateRoots commit_namespace_state(
        TrieDb &tdb, NamespacedStateDeltas const &ns_deltas,
        uint64_t const block_number, bytes32_t const &block_id)
    {
        CommitBuilder builder(block_number);
        builder.add_namespace_state_deltas(ns_deltas);
        return tdb.commit_namespace_state_deltas(
            block_id, builder, ns_deltas, block_number);
    }

    void expect_namespace_root_node(
        mpt::Db &db, TrieDb &tdb, mpt::NibblesView const prefix,
        uint64_t const ns, bytes32_t const &expected_root,
        uint64_t const block_number)
    {
        auto const res =
            db.find(tdb.get_root(), namespace_path(prefix, ns), block_number);
        ASSERT_TRUE(res.has_value());
        auto const data = res.value().node->data();
        ASSERT_EQ(data.size(), sizeof(bytes32_t));
        EXPECT_EQ(to_bytes(data), expected_root);
    }

    void expect_namespace_root_node(
        mpt::Db &db, TrieDb &tdb, uint64_t const ns,
        bytes32_t const &expected_root, uint64_t const block_number)
    {
        expect_namespace_root_node(
            db, tdb, finalized_nibbles, ns, expected_root, block_number);
    }

    bytes32_t
    root_for_namespace(NamespaceStateRoots const &roots, uint64_t const ns)
    {
        auto const it =
            std::find_if(roots.begin(), roots.end(), [ns](auto const &entry) {
                return entry.first == ns;
            });
        MONAD_ASSERT(it != roots.end());
        return it->second;
    }
}

template <typename TDB>
struct NamespaceWritePathTest : public TDB
{
    TrieDb tdb;

    NamespaceWritePathTest()
        : tdb{this->db}
    {
        seed_finalized_block_zero(this->db, tdb);
    }
};

TYPED_TEST_SUITE(NamespaceWritePathTest, DBTypes);

TYPED_TEST(NamespaceWritePathTest, namespace_raw_trie_insert)
{
    using namespace mpt;

    constexpr uint64_t ns{0x1111111111111111ULL};
    uint8_t ns_bytes[sizeof(uint64_t)];
    intx::be::store(ns_bytes, ns);
    auto const inner_hash = keccak256({ADDR_B.bytes, sizeof(ADDR_B.bytes)});
    auto const inner_value = encode_account_db(ADDR_B, Account{.balance = 42});

    std::deque<Update> alloc;
    std::deque<byte_string> bytes_alloc;

    UpdateList inner_list;
    inner_list.push_front(alloc.emplace_back(Update{
        .key = NibblesView{inner_hash},
        .value = bytes_alloc.emplace_back(inner_value),
        .next = UpdateList{},
        .version = 1}));

    UpdateList namespace_list;
    namespace_list.push_front(alloc.emplace_back(Update{
        .key = bytes_alloc.emplace_back(ns_bytes, sizeof(ns_bytes)),
        .value = byte_string_view{},
        .next = std::move(inner_list),
        .version = 1}));

    UpdateList state_list;
    state_list.push_front(alloc.emplace_back(Update{
        .key = namespace_state_nibbles,
        .value = byte_string_view{},
        .next = std::move(namespace_list),
        .version = 1}));

    UpdateList root_list;
    root_list.push_front(alloc.emplace_back(Update{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .next = std::move(state_list),
        .version = 1}));

    auto root = this->db.upsert({}, std::move(root_list), 1, true);

    auto const inner_key = concat(
        finalized_nibbles,
        NAMESPACE_STATE_NIBBLE,
        NibblesView{to_byte_string_view(ns_bytes)},
        NibblesView{inner_hash});
    auto inner_res = this->db.find(root, inner_key, 1);
    EXPECT_TRUE(inner_res.has_value()) << "inner account not found";
}

TYPED_TEST(NamespaceWritePathTest, namespace_commit_empty_inner_deltas)
{
    constexpr uint64_t ns{0x1212121212121212ULL};
    NamespacedStateDeltas ns_deltas;
    NamespacedStateDeltas::accessor ns_it{};
    ns_deltas.emplace(ns_it, ns, StateDeltas{});
    ns_it.release();

    auto const roots =
        commit_namespace_state(this->tdb, ns_deltas, 1, bytes32_t{1});

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, ns);
    EXPECT_EQ(roots[0].second, NULL_ROOT);
}

TYPED_TEST(
    NamespaceWritePathTest, namespace_commit_account_root_matches_plain_state)
{
    constexpr uint64_t ns{0x2222222222222222ULL};
    StateDeltas inner;
    StateDelta const delta{
        .account = {std::nullopt, Account{.balance = 42}}, .storage = {}};
    add_state_delta(inner, ADDR_A, delta);

    mpt::Db expected_db{std::make_unique<InMemoryMachine>()};
    TrieDb expected_tdb{expected_db};
    auto const expected_root =
        commit_plain_state_root(expected_tdb, inner, 1, bytes32_t{1});

    NamespacedStateDeltas ns_deltas;
    add_namespace_state_delta(ns_deltas, ns, ADDR_A, delta);
    auto const roots =
        commit_namespace_state(this->tdb, ns_deltas, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, ns);
    EXPECT_EQ(roots[0].second, expected_root);
    expect_namespace_root_node(this->db, this->tdb, ns, expected_root, 1);

    auto const account_res = this->db.find(
        this->tdb.get_root(), namespace_account_path(ns, ADDR_A), 1);
    ASSERT_TRUE(account_res.has_value());
    auto encoded_account = account_res.value().node->value();
    auto const decoded = decode_account_db_ignore_address(encoded_account);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value().balance, 42);
}

TYPED_TEST(
    NamespaceWritePathTest, namespace_commit_storage_root_matches_plain_state)
{
    constexpr uint64_t ns{0x3333333333333333ULL};
    Account const account{.balance = 100};
    StateDeltas inner;
    StateDelta const delta{
        .account = {std::nullopt, account},
        .storage = {{key1, {bytes32_t{}, value1}}}};
    add_state_delta(inner, ADDR_A, delta);

    mpt::Db expected_db{std::make_unique<InMemoryMachine>()};
    TrieDb expected_tdb{expected_db};
    auto const expected_root =
        commit_plain_state_root(expected_tdb, inner, 1, bytes32_t{1});

    NamespacedStateDeltas ns_deltas;
    add_namespace_state_delta(ns_deltas, ns, ADDR_A, delta);
    auto const roots =
        commit_namespace_state(this->tdb, ns_deltas, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, ns);
    EXPECT_EQ(roots[0].second, expected_root);
    expect_namespace_root_node(this->db, this->tdb, ns, expected_root, 1);

    auto const storage_res = this->db.find(
        this->tdb.get_root(), namespace_storage_path(ns, ADDR_A, key1), 1);
    ASSERT_TRUE(storage_res.has_value());
    auto encoded_storage = storage_res.value().node->value();
    auto const decoded = decode_storage_db(encoded_storage);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value().first, key1);
    EXPECT_EQ(decoded.value().second, value1);
}

TYPED_TEST(NamespaceWritePathTest, namespace_commit_multiple_namespaces)
{
    constexpr uint64_t namespace_1{0x5151515151515151ULL};
    constexpr uint64_t namespace_2{0x5252525252525252ULL};
    StateDelta const delta1{
        .account = {std::nullopt, Account{.balance = 111}}, .storage = {}};
    StateDelta const delta2{
        .account = {std::nullopt, Account{.balance = 222}}, .storage = {}};

    StateDeltas inner1;
    add_state_delta(inner1, ADDR_A, delta1);
    mpt::Db expected_db1{std::make_unique<InMemoryMachine>()};
    TrieDb expected_tdb1{expected_db1};
    auto const expected_root1 =
        commit_plain_state_root(expected_tdb1, inner1, 1, bytes32_t{1});

    StateDeltas inner2;
    add_state_delta(inner2, ADDR_B, delta2);
    mpt::Db expected_db2{std::make_unique<InMemoryMachine>()};
    TrieDb expected_tdb2{expected_db2};
    auto const expected_root2 =
        commit_plain_state_root(expected_tdb2, inner2, 1, bytes32_t{1});

    NamespacedStateDeltas ns_deltas;
    add_namespace_state_delta(ns_deltas, namespace_1, ADDR_A, delta1);
    add_namespace_state_delta(ns_deltas, namespace_2, ADDR_B, delta2);
    auto const roots =
        commit_namespace_state(this->tdb, ns_deltas, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);

    ASSERT_EQ(roots.size(), 2);
    EXPECT_EQ(root_for_namespace(roots, namespace_1), expected_root1);
    EXPECT_EQ(root_for_namespace(roots, namespace_2), expected_root2);
    expect_namespace_root_node(
        this->db, this->tdb, namespace_1, expected_root1, 1);
    expect_namespace_root_node(
        this->db, this->tdb, namespace_2, expected_root2, 1);
}

TYPED_TEST(NamespaceWritePathTest, namespace_commit_root_changes_across_writes)
{
    constexpr uint64_t ns{0x4444444444444444ULL};
    mpt::Db expected_db{std::make_unique<InMemoryMachine>()};
    TrieDb expected_tdb{expected_db};

    StateDeltas inner_1;
    StateDelta const delta_1{
        .account = {std::nullopt, Account{.balance = 10}}, .storage = {}};
    add_state_delta(inner_1, ADDR_A, delta_1);
    auto const expected_root_1 =
        commit_plain_state_root(expected_tdb, inner_1, 1, bytes32_t{1});

    NamespacedStateDeltas ns_deltas_1;
    add_namespace_state_delta(ns_deltas_1, ns, ADDR_A, delta_1);
    auto const roots_1 =
        commit_namespace_state(this->tdb, ns_deltas_1, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);
    ASSERT_EQ(roots_1.size(), 1);
    EXPECT_EQ(roots_1[0].second, expected_root_1);

    StateDeltas inner_2;
    StateDelta const delta_2{
        .account = {Account{.balance = 10}, Account{.balance = 20}},
        .storage = {}};
    add_state_delta(inner_2, ADDR_A, delta_2);
    auto const expected_root_2 =
        commit_plain_state_root(expected_tdb, inner_2, 2, bytes32_t{2});

    NamespacedStateDeltas ns_deltas_2;
    add_namespace_state_delta(ns_deltas_2, ns, ADDR_A, delta_2);
    auto const roots_2 =
        commit_namespace_state(this->tdb, ns_deltas_2, 2, bytes32_t{2});
    this->tdb.finalize(2, bytes32_t{2});
    this->tdb.set_block_and_prefix(2);
    ASSERT_EQ(roots_2.size(), 1);
    EXPECT_EQ(roots_2[0].second, expected_root_2);
    EXPECT_NE(roots_1[0].second, roots_2[0].second);
    expect_namespace_root_node(this->db, this->tdb, ns, expected_root_2, 2);
}

TEST_F(OnDiskTrieDbFixture, namespace_commit_uses_proposal_prefix_and_finalizes)
{
    constexpr uint64_t ns{0x5353535353535353ULL};
    bytes32_t const block_id{1};
    TrieDb tdb{this->db};
    seed_finalized_block_zero(this->db, tdb);

    StateDeltas inner;
    StateDelta const delta{
        .account = {std::nullopt, Account{.balance = 333}}, .storage = {}};
    add_state_delta(inner, ADDR_A, delta);
    mpt::Db expected_db{std::make_unique<InMemoryMachine>()};
    TrieDb expected_tdb{expected_db};
    auto const expected_root =
        commit_plain_state_root(expected_tdb, inner, 1, block_id);

    NamespacedStateDeltas ns_deltas;
    add_namespace_state_delta(ns_deltas, ns, ADDR_A, delta);
    auto const roots = commit_namespace_state(tdb, ns_deltas, 1, block_id);

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].second, expected_root);
    expect_namespace_root_node(
        this->db, tdb, proposal_prefix(block_id), ns, expected_root, 1);

    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);
    expect_namespace_root_node(this->db, tdb, ns, expected_root, 1);
}

TEST(DBTest, read_only)
{
    auto const name =
        std::filesystem::temp_directory_path() /
        (::testing::UnitTest::GetInstance()->current_test_info()->name() +
         std::to_string(rand()));
    {
        mpt::Db db{
            std::make_unique<OnDiskMachine>(),
            mpt::OnDiskDbConfig{.dbname_paths = {name}}};
        TrieDb rw(db);

        Account const acct1{.nonce = 1};
        commit_sequential(
            rw,
            StateDeltas(
                {{ADDR_A,
                  StateDelta{
                      .account = {std::nullopt, acct1}, .storage = {}}}}),
            Code{},
            BlockHeader{.number = 0});
        Account const acct2{.nonce = 2};
        commit_sequential(
            rw,
            StateDeltas(
                {{ADDR_A,
                  StateDelta{.account = {acct1, acct2}, .storage = {}}}}),
            Code{},
            BlockHeader{.number = 1});

        mpt::AsyncIOContext io_ctx{
            mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {name}}};
        mpt::Db ro_db{io_ctx};
        TrieDb ro{ro_db};
        ASSERT_EQ(ro.get_block_number(), 1);
        EXPECT_EQ(ro.read_account(ADDR_A), Account{.nonce = 2});
        ro.set_block_and_prefix(0);
        EXPECT_EQ(ro.read_account(ADDR_A), Account{.nonce = 1});

        Account const acct3{.nonce = 3};
        commit_sequential(
            rw,
            StateDeltas(
                {{ADDR_A,
                  StateDelta{.account = {acct2, acct3}, .storage = {}}}}),
            Code{},
            BlockHeader{.number = 2});
        // Read block 0
        EXPECT_EQ(ro.read_account(ADDR_A), Account{.nonce = 1});
        // Go forward to block 2
        ro.set_block_and_prefix(2);
        EXPECT_EQ(ro.read_account(ADDR_A), Account{.nonce = 3});
        // Go backward to block 1
        ro.set_block_and_prefix(1);
        EXPECT_EQ(ro.read_account(ADDR_A), Account{.nonce = 2});
        // Setting the same block number is no-op.
        ro.set_block_and_prefix(1);
        EXPECT_EQ(ro.read_account(ADDR_A), Account{.nonce = 2});
    }
    std::filesystem::remove(name);
}

TYPED_TEST(DBTest, read_storage)
{
    Account acct{.nonce = 1};
    TrieDb tdb{this->db};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage = {{key1, {bytes32_t{}, value1}}}}}}),
        Code{},
        BlockHeader{});

    // Existing storage
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{0, 0}, key1), value1);
    EXPECT_EQ(
        read_storage_and_slot(
            tdb.get_root(), this->db, tdb.get_block_number(), ADDR_A, key1)
            .first,
        key1);

    // Non-existing key
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{0, 0}, key2), bytes32_t{});
    EXPECT_EQ(
        read_storage_and_slot(
            tdb.get_root(), this->db, tdb.get_block_number(), ADDR_A, key2)
            .first,
        bytes32_t{});

    // Non-existing account
    EXPECT_FALSE(tdb.read_account(ADDR_B).has_value());
    EXPECT_EQ(tdb.read_storage(ADDR_B, Incarnation{0, 0}, key1), bytes32_t{});
    EXPECT_EQ(
        read_storage_and_slot(
            tdb.get_root(), this->db, tdb.get_block_number(), ADDR_B, key1)
            .first,
        bytes32_t{});
}

TYPED_TEST(DBTest, read_code)
{
    Account acct_a{.balance = 1, .code_hash = A_CODE_HASH, .nonce = 1};
    TrieDb tdb{this->db};
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_A, StateDelta{.account = {std::nullopt, acct_a}}}}),
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    auto const a_icode = tdb.read_code(A_CODE_HASH);
    EXPECT_EQ(byte_string_view(a_icode->code(), a_icode->size()), A_CODE);

    Account acct_b{.balance = 0, .code_hash = B_CODE_HASH, .nonce = 1};
    commit_sequential(
        tdb,
        StateDeltas({{ADDR_B, StateDelta{.account = {std::nullopt, acct_b}}}}),
        Code{{B_CODE_HASH, B_ICODE}},
        BlockHeader{.number = 1});

    auto const b_icode = tdb.read_code(B_CODE_HASH);
    EXPECT_EQ(byte_string_view(b_icode->code(), b_icode->size()), B_CODE);
}

TEST_F(OnDiskTrieDbFixture, get_proposal_block_ids)
{
    TrieDb tdb{db};
    tdb.reset_root(
        load_header(tdb.get_root(), db, BlockHeader{.number = 8}), 8);
    EXPECT_TRUE(get_proposal_block_ids(db, 8).empty());

    tdb.set_block_and_prefix(8);
    auto const round9_block_id = commit_sequential(
        tdb, StateDeltas({}), Code{}, BlockHeader{.number = 9});
    EXPECT_EQ(db.get_latest_finalized_version(), 9);
    {
        auto const proposals = get_proposal_block_ids(db, 9);
        EXPECT_EQ(proposals.size(), 1);
        EXPECT_EQ(proposals.front(), round9_block_id);
    }

    std::set<bytes32_t> block_ids;
    tdb.set_block_and_prefix(9); // block 9 finalized
    BlockHeader const header0{.number = 10};
    bytes32_t const block_id0{header0.number};
    block_ids.emplace(block_id0);
    commit_simple(tdb, StateDeltas({}), Code{}, block_id0, header0);
    {
        auto const proposals = get_proposal_block_ids(db, 10);
        EXPECT_EQ(std::set(proposals.begin(), proposals.end()), block_ids);
    }
    tdb.set_block_and_prefix(9);
    BlockHeader const header1{.number = 10};
    bytes32_t const block_id1{header1.number};
    block_ids.emplace(block_id1);
    commit_simple(tdb, StateDeltas({}), Code{}, block_id1, header1);
    {
        auto const proposals = get_proposal_block_ids(db, 10);
        EXPECT_EQ(std::set(proposals.begin(), proposals.end()), block_ids);
    }

    tdb.set_block_and_prefix(9);
    BlockHeader const header2{.number = 10};
    bytes32_t const block_id2{header2.number};
    block_ids.emplace(block_id2);
    commit_simple(tdb, StateDeltas({}), Code{}, block_id2, header2);

    tdb.finalize(10, block_id0);
    EXPECT_EQ(db.get_latest_finalized_version(), 10);
    {
        auto proposals = get_proposal_block_ids(db, 10);
        EXPECT_EQ(std::set(proposals.begin(), proposals.end()), block_ids);
    }
}

TYPED_TEST(DBTest, ModifyStorageOfAccount)
{
    Account acct{.balance = 1'000'000, .code_hash = {}, .nonce = 1337};
    TrieDb tdb{this->db};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{key1, {bytes32_t{}, value1}},
                       {key2, {bytes32_t{}, value2}}}}}}),
        Code{},
        BlockHeader{.number = 0});

    acct = tdb.read_account(ADDR_A).value();
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {acct, acct},
                  .storage = {{key2, {value2, value1}}}}}}),
        Code{},
        BlockHeader{.number = 1});

    EXPECT_EQ(
        tdb.state_root(),
        0x6303ffa4281cd596bc9fbfc21c28c1721ee64ec8e0f5753209eb8a13a739dae8_bytes32);
}

TYPED_TEST(DBTest, touch_without_modify_regression)
{
    TrieDb tdb{this->db};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A, StateDelta{.account = {std::nullopt, std::nullopt}}}}),
        Code{},
        BlockHeader{});

    EXPECT_EQ(tdb.read_account(ADDR_A), std::nullopt);
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, delete_account_modify_storage_regression)
{
    Account acct{.balance = 1'000'000, .code_hash = {}, .nonce = 1337};
    TrieDb tdb{this->db};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{key1, {bytes32_t{}, value1}},
                       {key2, {bytes32_t{}, value2}}}}}}),
        Code{},
        BlockHeader{.number = 0});

    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {acct, std::nullopt},
                  .storage =
                      {{key1, {value1, value2}}, {key2, {value2, value1}}}}}}),
        Code{},
        BlockHeader{.number = 1});

    EXPECT_EQ(tdb.read_account(ADDR_A), std::nullopt);
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{0, 0}, key1), bytes32_t{});
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, storage_deletion)
{
    Account acct{.balance = 1'000'000, .code_hash = {}, .nonce = 1337};

    TrieDb tdb{this->db};
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, acct},
                  .storage =
                      {{key1, {bytes32_t{}, value1}},
                       {key2, {bytes32_t{}, value2}}}}}}),
        Code{},
        BlockHeader{.number = 0});

    acct = tdb.read_account(ADDR_A).value();
    commit_sequential(
        tdb,
        StateDeltas(
            {{ADDR_A,
              StateDelta{
                  .account = {acct, acct},
                  .storage = {{key1, {value1, bytes32_t{}}}}}}}),
        Code{},
        BlockHeader{.number = 1});

    EXPECT_EQ(
        tdb.state_root(),
        0x1f54a52a44ffa5b8298f7ed596dea62455816e784dce02d79ea583f3a4146598_bytes32);
}

TYPED_TEST(DBTest, commit_receipts_transactions)
{

    TrieDb tdb{this->db};
    // empty receipts
    commit_sequential(tdb, StateDeltas({}), Code{}, BlockHeader{});
    EXPECT_EQ(tdb.receipts_root(), NULL_ROOT);

    std::vector<Receipt> receipts;
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 21'000, .type = TransactionType::legacy});
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 42'000, .type = TransactionType::legacy});

    // receipt with log
    Receipt rct{
        .status = 1, .gas_used = 65'092, .type = TransactionType::legacy};
    rct.add_log(Receipt::Log{
        .data =
            0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000043b2126e7a22e0c288dfb469e3de4d2c097f3ca0000000000000000000000000000000000000000000000001195387bce41fd4990000000000000000000000000000000000000000000000000000000000000000_bytes,
        .topics =
            {0xf341246adaac6f497bc2a656f546ab9e182111d630394f0c57c710a59a2cb567_bytes32},
        .address = 0x8d12a197cb00d4747a1fe03395095ce2a5cc6819_address});
    receipts.push_back(std::move(rct));

    std::vector<Transaction> transactions;
    std::vector<hash256> tx_hash;
    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};
    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};

    Transaction t1{
        .sc = {.signature = {.r = r, .s = s}}, // no chain_id in legacy txs
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value};
    Transaction t2{
        .sc = {.signature = {.r = r, .s = s}, .chain_id = 5}, // Goerli
        .nonce = 10,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value,
        .to = to_addr};
    Transaction t3 = t2;
    t3.nonce = 11;
    tx_hash.emplace_back(
        keccak256(rlp::encode_transaction(transactions.emplace_back(t1))));
    tx_hash.emplace_back(
        keccak256(rlp::encode_transaction(transactions.emplace_back(t2))));
    tx_hash.emplace_back(
        keccak256(rlp::encode_transaction(transactions.emplace_back(t3))));
    ASSERT_EQ(receipts.size(), transactions.size());

    std::vector<std::vector<CallFrame>> call_frames;
    call_frames.resize(receipts.size());
    constexpr uint64_t first_block = 1;
    std::vector<Address> senders = recover_senders(transactions);
    commit_sequential(
        tdb,
        StateDeltas({}),
        Code{},
        BlockHeader{.number = first_block},
        receipts,
        call_frames,
        senders,
        transactions);
    EXPECT_EQ(
        tdb.receipts_root(),
        0x7ea023138ee7d80db04eeec9cf436dc35806b00cc5fe8e5f611fb7cf1b35b177_bytes32);
    EXPECT_EQ(
        tdb.transactions_root(),
        0xfb4fce4331706502d2893deafe470d4cc97b4895294f725ccb768615a5510801_bytes32);

    auto verify_read_and_parse_receipt = [&](uint64_t const block_id) {
        size_t log_i = 0;
        for (unsigned i = 0; i < receipts.size(); ++i) {
            auto find_res = this->db.find(
                tdb.get_root(),
                mpt::concat(
                    FINALIZED_NIBBLE,
                    RECEIPT_NIBBLE,
                    mpt::NibblesView{rlp::encode_unsigned<unsigned>(i)}),
                block_id);
            ASSERT_TRUE(find_res.has_value());
            auto node_value = find_res.value().node->value();
            auto const decode_res = decode_receipt_db(node_value);
            ASSERT_TRUE(decode_res.has_value());
            auto const [receipt, log_index_begin] = decode_res.value();
            EXPECT_EQ(receipt, receipts[i]) << i;
            EXPECT_EQ(log_index_begin, log_i);
            log_i += receipt.logs.size();
        }
    };

    auto verify_read_and_parse_transaction = [&](uint64_t const block_id) {
        for (unsigned i = 0; i < transactions.size(); ++i) {
            auto find_res = this->db.find(
                tdb.get_root(),
                mpt::concat(
                    FINALIZED_NIBBLE,
                    TRANSACTION_NIBBLE,
                    mpt::NibblesView{rlp::encode_unsigned<unsigned>(i)}),
                block_id);
            ASSERT_TRUE(find_res.has_value());
            auto node_value = find_res.value().node->value();
            auto const decode_res = decode_transaction_db(node_value);
            ASSERT_TRUE(decode_res.has_value());
            auto const [tx, sender] = decode_res.value();
            EXPECT_EQ(tx, transactions[i]) << i;
            EXPECT_EQ(sender, senders[i]) << i;
        }
    };
    auto verify_tx_hash = [&](hash256 const &tx_hash,
                              uint64_t const block_id,
                              unsigned const tx_idx) {
        auto const find_res = this->db.find(
            tdb.get_root(),
            concat(FINALIZED_NIBBLE, TX_HASH_NIBBLE, mpt::NibblesView{tx_hash}),
            tdb.get_block_number());
        EXPECT_TRUE(find_res.has_value());
        EXPECT_EQ(
            find_res.value().node->value(),
            rlp::encode_list2(
                rlp::encode_unsigned(block_id), rlp::encode_unsigned(tx_idx)));
    };
    verify_tx_hash(tx_hash[0], first_block, 0);
    verify_tx_hash(tx_hash[1], first_block, 1);
    verify_tx_hash(tx_hash[2], first_block, 2);
    verify_read_and_parse_receipt(first_block);
    verify_read_and_parse_transaction(first_block);

    // A new receipt trie with eip1559 transaction type
    constexpr uint64_t second_block = 2;
    receipts.clear();
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 34865, .type = TransactionType::eip1559});
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 77969, .type = TransactionType::eip1559});
    transactions.clear();
    t1.nonce = 12;
    t2.nonce = 13;
    tx_hash.emplace_back(
        keccak256(rlp::encode_transaction(transactions.emplace_back(t1))));
    tx_hash.emplace_back(
        keccak256(rlp::encode_transaction(transactions.emplace_back(t2))));
    ASSERT_EQ(receipts.size(), transactions.size());
    call_frames.resize(receipts.size());
    senders = recover_senders(transactions);
    commit_sequential(
        tdb,
        StateDeltas({}),
        Code{},
        BlockHeader{.number = second_block},
        receipts,
        call_frames,
        senders,
        transactions);
    EXPECT_EQ(
        tdb.receipts_root(),
        0x61f9b4707b28771a63c1ac6e220b2aa4e441dd74985be385eaf3cd7021c551e9_bytes32);
    EXPECT_EQ(
        tdb.transactions_root(),
        0x0800aa3014aaa87b4439510e1206a7ef2568337477f0ef0c444cbc2f691e52cf_bytes32);
    verify_tx_hash(tx_hash[0], first_block, 0);
    verify_tx_hash(tx_hash[1], first_block, 1);
    verify_tx_hash(tx_hash[2], first_block, 2);
    verify_tx_hash(tx_hash[3], second_block, 0);
    verify_tx_hash(tx_hash[4], second_block, 1);
    verify_read_and_parse_receipt(second_block);
    verify_read_and_parse_transaction(second_block);
}

TEST_F(OnDiskTrieDbWithFileFixture, get_transactions)
{

    TrieDb tdb{this->db};

    static constexpr auto price{20'000'000'000};
    static constexpr auto value{0xde0b6b3a7640000_u256};
    static constexpr auto r{
        0x28ef61340bd939bc2195fe537567866003e1a15d3c71ff63e1590620aa636276_u256};
    static constexpr auto s{
        0x67cbe9d8997f761aecb703304b3800ccf555c9f3dc64214b297fb1966a3b6d83_u256};
    static constexpr auto to_addr{
        0x3535353535353535353535353535353535353535_address};

    constexpr uint64_t block_number = 0;
    constexpr unsigned total_txs = 4096;
    std::vector<Transaction> transactions;
    transactions.reserve(total_txs);
    Transaction tx{
        .sc = {.signature = {.r = r, .s = s}}, // no chain_id in legacy txs
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value,
        .to = to_addr};
    for (unsigned i = 0; i < total_txs; ++i) {
        transactions.emplace_back(tx);
        tx.nonce++;
    }
    std::vector<std::vector<CallFrame>> call_frames;
    std::vector<Receipt> receipts;
    receipts.resize(transactions.size());
    call_frames.resize(receipts.size());
    std::vector<Address> senders = recover_senders(transactions);
    commit_sequential(
        tdb,
        StateDeltas({}),
        Code{},
        BlockHeader{.number = block_number},
        receipts,
        call_frames,
        senders,
        transactions);

    auto verify_transactions = [&](auto &db) {
        auto const txs_res = get_transactions(db, block_number);
        ASSERT_TRUE(txs_res.has_value());
        auto const txs = txs_res.value();
        EXPECT_EQ(txs.size(), transactions.size());
        for (size_t i = 0; i < txs.size(); ++i) {
            EXPECT_EQ(txs[i], transactions[i]);
        }
    };

    // RWDb
    verify_transactions(this->db);

    { // nonblocking RODb
        mpt::RODb rodb{
            mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {this->dbname}}};
        verify_transactions(rodb);
    }

    { // blocking read-only Db
        mpt::AsyncIOContext io_ctx{
            mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {this->dbname}}};
        mpt::Db rodb{io_ctx};
        verify_transactions(rodb);
    }
}

TYPED_TEST(DBTest, to_json)
{
    // TODO: typed test doesn't really make sense here, split to two different
    // tests
    std::filesystem::path dbname{};
    if (this->on_disk) {
        dbname = {
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_test_db_to_json"};
    }
    auto db = [&] {
        if (this->on_disk) {
            return mpt::Db{
                std::make_unique<OnDiskMachine>(),
                mpt::OnDiskDbConfig{.dbname_paths = {dbname}}};
        }
        return mpt::Db{std::make_unique<InMemoryMachine>()};
    }();
    TrieDb tdb{db};
    load_db(tdb, 0);

    auto const expected_payload = nlohmann::json::parse(R"(
{
  "0x03601462093b5945d1676df093446790fd31b20e7b12a2e8e5e09d068109616b": {
    "balance": "838137708090664833",
    "code": "0x",
    "address": "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b",
    "nonce": "0x1",
    "storage": {}
  },
  "0x227a737497210f7cc2f464e3bfffadefa9806193ccdf873203cd91c8d3eab518": {
    "balance": "838137708091124174",
    "code":
    "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "address": "0x0000000000000000000000000000000000000100",
    "nonce": "0x0",
    "storage": {
      "0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563":
      {
        "slot": "0x0000000000000000000000000000000000000000000000000000000000000000",
        "value": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"
      }
    }
  },
  "0x4599828688a5c37132b6fc04e35760b4753ce68708a7b7d4d97b940047557fdb": {
    "balance": "838137708091124174",
    "code":
    "0x60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "address": "0x0000000000000000000000000000000000000101",
    "nonce": "0x0",
    "storage": {}
  },
  "0x4c933a84259efbd4fb5d1522b5255e6118da186a2c71ec5efaa5c203067690b7": {
    "balance": "838137708091124174",
    "code":
    "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60010160005500",
    "address": "0x0000000000000000000000000000000000000104",
    "nonce": "0x0",
    "storage": {}
  },
  "0x9d860e7bb7e6b09b87ab7406933ef2980c19d7d0192d8939cf6dc6908a03305f": {
    "balance": "459340",
    "code": "0x",
    "address": "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba",
    "nonce": "0x0",
    "storage": {}
  },
  "0xa17eacbc25cda025e81db9c5c62868822c73ce097cee2a63e33a2e41268358a1": {
    "balance": "838137708091124174",
    "code":
    "0x60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "address": "0x0000000000000000000000000000000000000102",
    "nonce": "0x0",
    "storage": {}
  },
  "0xa5cc446814c4e9060f2ecb3be03085683a83230981ca8f19d35a4438f8c2d277": {
    "balance": "838137708091124174",
    "code": "0x600060000160005500",
    "address": "0x0000000000000000000000000000000000000103",
    "nonce": "0x0",
    "storage": {}
  },
  "0xf057b39b049c7df5dfa86c4b0869abe798cef059571a5a1e5bbf5168cf6c097b": {
    "balance": "838137708091124175",
    "code": "0x600060006000600060006004356101000162fffffff100",
    "address": "0xcccccccccccccccccccccccccccccccccccccccc",
    "nonce": "0x0",
    "storage": {}
  }
})");

    // RWDb or in memory Db
    EXPECT_EQ(expected_payload, tdb.to_json());
    if (this->on_disk) {
        // also test to_json from a read only db
        mpt::AsyncIOContext io_ctx{
            mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
        mpt::Db ro_db{io_ctx};
        TrieDb ro{ro_db};
        EXPECT_EQ(expected_payload, ro.to_json());

        std::filesystem::remove(dbname);
    }
}

TYPED_TEST(DBTest, load_from_binary)
{
    std::ifstream accounts(test_resource::checkpoint_dir / "accounts");
    std::ifstream code(test_resource::checkpoint_dir / "code");
    auto root = load_from_binary(this->db, accounts, code);
    TrieDb tdb{this->db};
    tdb.reset_root(root, 0);
    EXPECT_EQ(
        tdb.state_root(),
        0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32);
    auto const a_icode = tdb.read_code(A_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(a_icode->code(), a_icode->size()),
        byte_string_view(A_ICODE->code(), A_ICODE->size()));
    auto const b_icode = tdb.read_code(B_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(b_icode->code(), b_icode->size()),
        byte_string_view(B_ICODE->code(), B_ICODE->size()));
    auto const c_icode = tdb.read_code(C_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(c_icode->code(), c_icode->size()),
        byte_string_view(C_ICODE->code(), C_ICODE->size()));
    auto const d_icode = tdb.read_code(D_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(d_icode->code(), d_icode->size()),
        byte_string_view(D_ICODE->code(), D_ICODE->size()));
    auto const e_icode = tdb.read_code(E_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(e_icode->code(), e_icode->size()),
        byte_string_view(E_ICODE->code(), E_ICODE->size()));
    auto const h_icode = tdb.read_code(H_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(h_icode->code(), h_icode->size()),
        byte_string_view(H_ICODE->code(), H_ICODE->size()));
}

TYPED_TEST(DBTest, commit_call_frames)
{
    TrieDb tdb{this->db};

    CallFrame const call_frame1{
        .type = CallType::CALL,
        .flags = 1, // static call
        .from = ADDR_A,
        .to = ADDR_B,
        .value = 11'111u,
        .gas = 100'000u,
        .gas_used = 21'000u,
        .input = byte_string{0xaa, 0xbb, 0xcc},
        .output = byte_string{},
        .status = EVMC_SUCCESS,
        .depth = 0,
    };

    CallFrame const call_frame2{
        .type = CallType::DELEGATECALL,
        .flags = 0,
        .from = ADDR_B,
        .to = ADDR_A,
        .value = 0,
        .gas = 10'000u,
        .gas_used = 10'000u,
        .input = byte_string{0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0x01},
        .output = byte_string{0x01, 0x02},
        .status = EVMC_REVERT,
        .depth = 1,
    };

    constexpr uint64_t NUM_TXNS = 1000;

    static byte_string const encoded_txn = byte_string{0x1a, 0x1b, 0x1c};
    std::vector<CallFrame> const call_frame{call_frame1, call_frame2};
    std::vector<std::vector<CallFrame>> call_frames;
    for (uint64_t txn = 0; txn < NUM_TXNS; ++txn) {
        call_frames.emplace_back(call_frame);
    }
    std::vector<Receipt> const receipts(call_frames.size());
    // need to increment the nonce of transactions
    std::vector<Transaction> transactions;
    for (uint64_t nonce = 0; nonce < call_frames.size(); ++nonce) {
        transactions.push_back(Transaction{.nonce = nonce});
    }
    std::vector<Address> const senders{call_frames.size()};
    commit_sequential(
        tdb,
        StateDeltas({}),
        Code{},
        BlockHeader{},
        receipts,
        call_frames,
        senders,
        transactions);

    for (uint64_t txn = 0; txn < NUM_TXNS; ++txn) {
        auto const &res = read_call_frame(
            tdb.get_root(), this->db, tdb.get_block_number(), txn);
        ASSERT_TRUE(!res.empty());
        ASSERT_TRUE(res.size() == 2);
        EXPECT_EQ(res[0], call_frame1);
        EXPECT_EQ(res[1], call_frame2);
    }
}
