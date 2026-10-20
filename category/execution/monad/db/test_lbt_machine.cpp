// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/async/detail/scope_polyfill.hpp>
#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/lbt_machine.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/lbt/commit.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/test/lbt_test_support.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <array>
#include <cstdint>
#include <filesystem>
#include <map>
#include <memory>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::literals;
using namespace monad::mpt;
using namespace monad::test;

namespace
{
    // A change to any of these is a change of state commitment.
    constexpr bytes32_t PIN_STATE_ROOT_MATCHES_REFERENCE{
        0x21fdd01aad48ffb77fe0f32c921568dc25099b677ebb2527b8914230942b660e_bytes32};
    constexpr bytes32_t PIN_STORAGE_EMPTIED{
        0xb6af3b4f6119a7cf20e2aa296c525e40778a44f16352d60f0f5bf74ee39192cf_bytes32};
    constexpr bytes32_t PIN_REINCARNATION_WIPES_STORAGE{
        0x0d02e44198fe2d87e1dbc9a2898f03333e6aeaea756f9ef4b8581885998ea10b_bytes32};
    constexpr bytes32_t PIN_ON_DISK_REOPEN{
        0xb802502bc674891339e5452cbc68cdedf0baf2a949bedf9a1a2d719bdf48f2bc_bytes32};
    constexpr bytes32_t PIN_THREE_ACCOUNTS{
        0x4f7a6ca1d27d0bc451c43b344bfbacaea6117015c8a58ca4ac306e6359495008_bytes32};
    constexpr bytes32_t PIN_ERASE_LIFTS_ACCOUNT_AND_PAGE{
        0x9568e8d0bcc2067a5096ed1a8035bbc0c8ddc27f75a08e2cbcc2dbc4170199e4_bytes32};
    constexpr bytes32_t PIN_PROPOSAL_ROOT{
        0x4f13545a3e1e74234cf30669e541139b9c1a685f801bf7b703f21a95b145aee3_bytes32};

    struct ExpectedAccount
    {
        Address addr;
        std::vector<bytes32_t> page_keys; // all of the account's pages
    };

    // Rebuilds the expected state root from the raw leaves in the db, using
    // the reference trie for structure. Also checks each account's cached
    // storage root.
    bytes32_t expected_state_root(
        mpt::Db &db, TrieDb const &tdb, uint64_t const block,
        std::vector<ExpectedAccount> const &accounts)
    {
        NodeCursor const root{tdb.get_root()};
        ReferenceTrie account_trie;
        for (auto const &acct : accounts) {
            auto const ah = keccak256(acct.addr.bytes);
            auto const account_path =
                concat(FINALIZED_NIBBLE, STATE_NIBBLE, NibblesView{ah});
            auto const account_node = db.find(root, account_path, block);
            EXPECT_TRUE(account_node.has_value());
            ReferenceTrie storage_trie;
            for (auto const &pk : acct.page_keys) {
                auto const ph = keccak256(pk.bytes);
                auto const page_node = db.find(
                    root,
                    concat(NibblesView{account_path}, NibblesView{ph}),
                    block);
                EXPECT_TRUE(page_node.has_value());
                auto const page = decode_storage_leaf_to_page(
                    page_node.value().node->value(), true);
                storage_trie.upsert(to_bytes(ph), page_commit(page));
            }
            byte_string account_bytes{account_node.value().node->value()};
            if (!acct.page_keys.empty()) {
                auto const storage_root = storage_trie.root();
                EXPECT_EQ(
                    to_bytes(account_node.value().node->data()), storage_root);
                account_bytes += byte_string_view{storage_root.bytes, 32};
            }
            else {
                EXPECT_TRUE(account_node.value().node->data().empty());
            }
            account_trie.upsert(to_bytes(ah), lbt::value_hash(account_bytes));
        }
        return account_trie.root();
    }

    void commit_block(
        mpt::Db &mpt_db, TrieDb &tdb, uint64_t const block,
        StateDeltas const &deltas)
    {
        PageCommitBuilder builder(block, tdb);
        builder.add_state_deltas(deltas);
        auto root = mpt_db.upsert(
            block == 0 ? nullptr : tdb.get_root(),
            builder.build(finalized_nibbles),
            block);
        tdb.reset_root(std::move(root), block);
    }

    template <class Machine>
    void walk(Machine &m, NibblesView const path)
    {
        for (unsigned i = 0; i < path.nibble_size(); ++i) {
            m.down(path.get(i));
        }
    }

    // Indices i < j whose keys share a first nibble, and k whose key does
    // not: the first such triple in 0, 1, 2, ...
    template <class KeyOf>
    std::array<uint64_t, 3> shared_first_nibble(KeyOf const &key_of)
    {
        std::array<std::optional<uint64_t>, 16> first_with{};
        for (uint64_t i = 0;; ++i) {
            unsigned const n = key_of(i).bytes[0] >> 4;
            if (!first_with[n].has_value()) {
                first_with[n] = i;
                continue;
            }
            for (unsigned m = 0; m < 16; ++m) {
                if (m != n && first_with[m].has_value()) {
                    return {*first_with[n], i, *first_with[m]};
                }
            }
        }
    }

    std::filesystem::path temp_pool_path(char const *const name)
    {
        return std::filesystem::temp_directory_path() /
               (std::string{name} + std::to_string(std::random_device{}()));
    }

    template <class Machine>
    mpt::Db make_db()
    {
        if constexpr (std::is_same_v<Machine, LbtOnDiskMachine>) {
            return mpt::Db{std::make_unique<Machine>(), OnDiskDbConfig{}};
        }
        else {
            return mpt::Db{std::make_unique<Machine>()};
        }
    }

    constexpr auto SLOT0 = bytes32_t{uint64_t{0}};
    constexpr auto SLOT1 = bytes32_t{uint64_t{1}};
    constexpr auto SLOT2 = bytes32_t{uint64_t{2}};
    constexpr auto SLOT_FAR = bytes32_t{uint64_t{0x1000}};
    constexpr auto V1 = bytes32_t{uint64_t{0xaaaa}};
    constexpr auto V2 = bytes32_t{uint64_t{0xbbbb}};
}

TEST(LbtMachine, kind_and_page_encoding)
{
    mpt::Db mpt_db{std::make_unique<LbtInMemoryMachine>()};
    TrieDb const tdb{mpt_db};
    EXPECT_EQ(mpt_db.state_machine_type(), state_machine_kind::lbt_binary);
    EXPECT_TRUE(tdb.is_page_encoded());
    EXPECT_EQ(LbtOnDiskMachine{}.kind(), state_machine_kind::lbt_binary);
}

TEST(LbtMachineDeathTest, unknown_kind_is_not_read_as_slots)
{
    EXPECT_DEATH(
        (void)is_page_encoded_kind(static_cast<state_machine_kind>(3)), "");
}

TEST(LbtMachine, on_disk_reopen_restores_kind)
{
    auto const dbname = temp_pool_path("lbt_machine_reopen_");
    auto const unfile =
        make_scope_exit([&]() noexcept { std::filesystem::remove(dbname); });
    OnDiskDbConfig const create_config{
        .dbname_path = dbname, .chunk_capacity = 24};
    Account const acct{.nonce = 1};
    StateDeltas const block0{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, acct},
             .storage = {
                 {SLOT0, {bytes32_t{}, V1}}, {SLOT_FAR, {bytes32_t{}, V2}}}}}};
    StateDeltas const block1{
        {ADDR_A,
         StateDelta{
             .account = {acct, acct}, .storage = {{SLOT1, {bytes32_t{}, V2}}}}},
        {ADDR_B, StateDelta{.account = {std::nullopt, acct}, .storage = {}}}};
    {
        mpt::Db mpt_db{std::make_unique<LbtOnDiskMachine>(), create_config};
        TrieDb tdb{mpt_db};
        commit_block(mpt_db, tdb, 0, block0);
        mpt_db.update_finalized_version(0);
        EXPECT_EQ(tdb.state_root(), PIN_ON_DISK_REOPEN);
    }

    mpt::Db never_closed_db{
        std::make_unique<LbtOnDiskMachine>(), OnDiskDbConfig{}};
    TrieDb never_closed{never_closed_db};
    commit_block(never_closed_db, never_closed, 0, block0);
    commit_block(never_closed_db, never_closed, 1, block1);

    register_lbt_state_machines();
    OnDiskDbConfig reopen_config = create_config;
    reopen_config.append = true;
    mpt::Db mpt_db{reopen_config};
    TrieDb tdb{mpt_db};
    EXPECT_EQ(mpt_db.state_machine_type(), state_machine_kind::lbt_binary);
    EXPECT_EQ(tdb.state_root(), PIN_ON_DISK_REOPEN);
    // Only hashing a new block exercises the machine the registry built.
    commit_block(mpt_db, tdb, 1, block1);
    EXPECT_EQ(tdb.state_root(), never_closed.state_root());
    EXPECT_EQ(
        tdb.state_root(),
        expected_state_root(
            mpt_db,
            tdb,
            1,
            {{ADDR_A, {compute_page_key(SLOT0), compute_page_key(SLOT_FAR)}},
             {ADDR_B, {}}}));
}

TEST(LbtMachine, rodb_reads_storage)
{
    auto const dbname = temp_pool_path("lbt_machine_rodb_");
    auto const unfile =
        make_scope_exit([&]() noexcept { std::filesystem::remove(dbname); });
    {
        mpt::Db mpt_db{
            std::make_unique<LbtOnDiskMachine>(),
            OnDiskDbConfig{.dbname_path = dbname, .chunk_capacity = 24}};
        TrieDb tdb{mpt_db};
        commit_block(
            mpt_db,
            tdb,
            0,
            StateDeltas{
                {ADDR_A,
                 StateDelta{
                     .account = {std::nullopt, Account{.nonce = 1}},
                     .storage = {{SLOT_FAR, {bytes32_t{}, V2}}}}}});
        mpt_db.update_finalized_version(0);
    }
    mpt::RODb rodb{ReadOnlyOnDiskDbConfig{.dbname_path = {dbname}}};
    TrieRODb trodb{rodb};
    trodb.set_block_and_prefix(0);
    EXPECT_TRUE(trodb.is_page_encoded());
    EXPECT_EQ(trodb.read_storage(ADDR_A, Incarnation{0, 0}, SLOT_FAR), V2);
}

TEST(LbtMachine, state_root_matches_reference)
{
    mpt::Db mpt_db{std::make_unique<LbtInMemoryMachine>()};
    TrieDb tdb{mpt_db};
    Account const acct{.nonce = 1};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{SLOT0, {bytes32_t{}, V1}},
                      {SLOT1, {bytes32_t{}, V2}},
                      {SLOT_FAR, {bytes32_t{}, V1}}}}},
            {ADDR_B,
             StateDelta{.account = {std::nullopt, acct}, .storage = {}}}});
    EXPECT_EQ(
        tdb.state_root(),
        expected_state_root(
            mpt_db,
            tdb,
            0,
            {{ADDR_A, {compute_page_key(SLOT0), compute_page_key(SLOT_FAR)}},
             {ADDR_B, {}}}));
    EXPECT_EQ(tdb.state_root(), PIN_STATE_ROOT_MATCHES_REFERENCE);
}

TEST(LbtMachine, three_accounts_match_reference)
{
    constexpr uint64_t NUM_PAGES = 16;
    Account const acct{.nonce = 1};
    StorageDeltas storage;
    std::vector<bytes32_t> page_keys;
    for (uint64_t i = 0; i < NUM_PAGES; ++i) {
        auto const slot = bytes32_t{i << 12};
        storage.insert({slot, {bytes32_t{}, V1}});
        page_keys.push_back(compute_page_key(slot));
    }
    StateDeltas const deltas{
        {ADDR_A,
         StateDelta{.account = {std::nullopt, acct}, .storage = storage}},
        {ADDR_B, StateDelta{.account = {std::nullopt, acct}, .storage = {}}},
        {ADDR_C,
         StateDelta{
             .account = {std::nullopt, acct},
             .storage = {{SLOT0, {bytes32_t{}, V2}}}}}};
    // ADDR_C's single page makes its storage root a lone leaf.
    std::vector<ExpectedAccount> const expected{
        {ADDR_A, page_keys}, {ADDR_B, {}}, {ADDR_C, {compute_page_key(SLOT0)}}};
    mpt::Db mpt_db{std::make_unique<LbtInMemoryMachine>()};
    TrieDb tdb{mpt_db};
    commit_block(mpt_db, tdb, 0, deltas);
    EXPECT_EQ(tdb.state_root(), expected_state_root(mpt_db, tdb, 0, expected));
    EXPECT_EQ(tdb.state_root(), PIN_THREE_ACCOUNTS);
}

TEST(LbtMachine, non_state_tables_keep_mpt_roots)
{
    Receipt receipt{
        .status = 1, .gas_used = 21'000, .type = TransactionType::legacy};
    receipt.add_log(Receipt::Log{
        .data = byte_string(3, 0x11), .topics = {V1}, .address = ADDR_B});
    std::vector<Receipt> const receipts{receipt};
    std::vector<Transaction> const transactions{Transaction{
        .sc = {.signature = {.r = 1, .s = 2}},
        .nonce = 9,
        .max_fee_per_gas = 20'000'000'000,
        .gas_limit = 21'000,
        .value = 1}};
    std::vector<Address> const senders{ADDR_A};
    std::vector<std::vector<CallFrame>> const call_frames(1);
    std::vector<Withdrawal> const withdrawals{Withdrawal{
        .index = 1, .validator_index = 2, .amount = 3, .recipient = ADDR_C}};
    StateDeltas const deltas{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, Account{.nonce = 10}},
             .storage = {{SLOT0, {bytes32_t{}, V1}}}}}};

    struct Roots
    {
        bytes32_t state;
        bytes32_t receipts;
        bytes32_t transactions;
        std::optional<bytes32_t> withdrawals;
    };

    auto const commit = [&](mpt::Db &db) {
        TrieDb tdb{db};
        commit_simple(
            tdb,
            deltas,
            Code{},
            bytes32_t{1},
            BlockHeader{.number = 0},
            receipts,
            call_frames,
            senders,
            transactions,
            {},
            withdrawals);
        return Roots{
            .state = tdb.state_root(),
            .receipts = tdb.receipts_root(),
            .transactions = tdb.transactions_root(),
            .withdrawals = tdb.withdrawals_root()};
    };
    mpt::Db monad_db{std::make_unique<MonadInMemoryMachine>()};
    mpt::Db lbt_db{std::make_unique<LbtInMemoryMachine>()};
    auto const mpt_roots = commit(monad_db);
    auto const lbt_roots = commit(lbt_db);
    EXPECT_NE(lbt_roots.state, mpt_roots.state);
    EXPECT_EQ(lbt_roots.receipts, mpt_roots.receipts);
    EXPECT_EQ(lbt_roots.transactions, mpt_roots.transactions);
    ASSERT_TRUE(mpt_roots.withdrawals.has_value());
    EXPECT_EQ(lbt_roots.withdrawals, mpt_roots.withdrawals);
}

// A proposal lives under a longer Db prefix than the finalized state; keys
// measured from the table give both the same root.
TEST(LbtMachine, proposal_root_matches_reference)
{
    mpt::Db mpt_db{std::make_unique<LbtOnDiskMachine>(), mpt::OnDiskDbConfig{}};
    TrieDb tdb{mpt_db};
    Account const acct{.nonce = 1};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {ADDR_B,
             StateDelta{.account = {std::nullopt, acct}, .storage = {}}}});
    mpt_db.update_finalized_version(0);
    tdb.set_block_and_prefix(0);
    bytes32_t const block_id{1};
    commit_simple(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{SLOT0, {bytes32_t{}, V1}},
                      {SLOT_FAR, {bytes32_t{}, V2}}}}}},
        Code{},
        block_id,
        BlockHeader{.number = 1});
    auto const proposal_root = tdb.state_root();
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);
    EXPECT_EQ(tdb.state_root(), proposal_root);
    EXPECT_EQ(
        proposal_root,
        expected_state_root(
            mpt_db,
            tdb,
            1,
            {{ADDR_A, {compute_page_key(SLOT0), compute_page_key(SLOT_FAR)}},
             {ADDR_B, {}}}));
    EXPECT_EQ(proposal_root, PIN_PROPOSAL_ROOT);
}

// Random blocks over a small address and slot space, so that keys collide
// at both trie levels and pages hold several slots, committed in lockstep to
// an in-memory and an on-disk pool.
TEST(LbtMachine, random_blocks_match_reference)
{
    struct LiveAccount
    {
        Account account;
        std::map<uint64_t, bytes32_t> slots;
    };

    std::mt19937_64 rng{11};
    auto const random_slot = [&rng] {
        uint64_t const page = rng() % 6;
        return page * 128 + rng() % 3;
    };
    auto const random_value = [&rng] { return bytes32_t{rng() | 1}; };
    std::map<uint64_t, LiveAccount> live;
    mpt::Db mem_db{std::make_unique<LbtInMemoryMachine>()};
    mpt::Db disk_db{std::make_unique<LbtOnDiskMachine>(), OnDiskDbConfig{}};
    TrieDb mem{mem_db};
    TrieDb disk{disk_db};
    for (uint64_t block = 0; block < 30; ++block) {
        StateDeltas deltas;
        std::set<uint64_t> touched;
        for (int op = 0; op < 6; ++op) {
            uint64_t const a = 1 + rng() % 48;
            if (!touched.insert(a).second) {
                continue;
            }
            Address const addr{a};
            auto const it = live.find(a);
            StorageDeltas storage;
            if (it == live.end()) {
                LiveAccount created;
                created.account.nonce = 1;
                created.account.balance = rng() % 1000;
                for (uint64_t n = rng() % 4; n > 0; --n) {
                    auto const s = random_slot();
                    auto const v = random_value();
                    if (created.slots.emplace(s, v).second) {
                        storage.emplace(bytes32_t{s}, StorageDelta{{}, v});
                    }
                }
                deltas.emplace(
                    addr,
                    StateDelta{
                        .account = {std::nullopt, created.account},
                        .storage = storage});
                live.emplace(a, std::move(created));
                continue;
            }
            auto &acct = it->second;
            Account const before = acct.account;
            switch (rng() % 6) {
            case 0:
                acct.account.balance += 1;
                break;
            case 1: {
                auto const s = random_slot();
                auto const v = random_value();
                auto &slot = acct.slots[s];
                storage.emplace(bytes32_t{s}, StorageDelta{slot, v});
                slot = v;
                break;
            }
            case 2:
                if (!acct.slots.empty()) {
                    auto const first = acct.slots.begin();
                    storage.emplace(
                        bytes32_t{first->first},
                        StorageDelta{first->second, {}});
                    acct.slots.erase(first);
                }
                break;
            case 3:
                // A new slot on a page the account already has.
                if (!acct.slots.empty()) {
                    auto const s = acct.slots.begin()->first ^ 1;
                    auto const v = random_value();
                    auto &slot = acct.slots[s];
                    storage.emplace(bytes32_t{s}, StorageDelta{slot, v});
                    slot = v;
                }
                break;
            case 4:
                for (auto const &[s, v] : acct.slots) {
                    storage.emplace(bytes32_t{s}, StorageDelta{v, {}});
                }
                deltas.emplace(
                    addr,
                    StateDelta{
                        .account = {before, std::nullopt}, .storage = storage});
                live.erase(it);
                continue;
            default: {
                acct.account.incarnation = Incarnation{block, 0};
                acct.slots.clear();
                auto const s = random_slot();
                auto const v = random_value();
                acct.slots[s] = v;
                storage.emplace(bytes32_t{s}, StorageDelta{{}, v});
                break;
            }
            }
            deltas.emplace(
                addr,
                StateDelta{
                    .account = {before, acct.account}, .storage = storage});
        }
        commit_block(mem_db, mem, block, deltas);
        commit_block(disk_db, disk, block, deltas);

        std::vector<ExpectedAccount> expected;
        for (auto const &[a, acct] : live) {
            std::set<bytes32_t> pages;
            for (auto const &[s, v] : acct.slots) {
                pages.insert(compute_page_key(bytes32_t{s}));
                ASSERT_EQ(
                    mem.read_storage(
                        Address{a}, acct.account.incarnation, bytes32_t{s}),
                    v);
            }
            expected.push_back(
                {Address{a},
                 std::vector<bytes32_t>{pages.begin(), pages.end()}});
        }
        auto const root =
            expected.empty()
                ? NULL_ROOT
                : expected_state_root(mem_db, mem, block, expected);
        ASSERT_EQ(mem.state_root(), root) << "block " << block;
        ASSERT_EQ(disk.state_root(), root) << "block " << block;
    }
}

template <class Machine>
struct LbtMachineTyped : public ::testing::Test
{
};

using LbtMachines = ::testing::Types<LbtInMemoryMachine, LbtOnDiskMachine>;
TYPED_TEST_SUITE(LbtMachineTyped, LbtMachines);

TYPED_TEST(LbtMachineTyped, state_key_prefix_starts_at_table_key)
{
    auto const ah = keccak256(ADDR_A.bytes);
    auto const sh = keccak256(compute_page_key(SLOT_FAR).bytes);
    NibblesView const account_key{ah};
    NibblesView const storage_key{sh};
    for (auto const &section :
         {finalized_nibbles, proposal_prefix(bytes32_t{7})}) {
        TypeParam m;
        walk(m, concat(NibblesView{section}, STATE_NIBBLE));
        EXPECT_EQ(m.state_key_prefix().nibble_size(), 0u);
        walk(m, account_key.substr(0, 10));
        EXPECT_EQ(m.state_key_prefix(), account_key.substr(0, 10));
        walk(m, account_key.substr(10));
        EXPECT_EQ(m.state_key_prefix(), account_key);
        walk(m, storage_key.substr(0, 1));
        EXPECT_EQ(m.state_key_prefix(), storage_key.substr(0, 1));
        walk(m, storage_key.substr(1));
        EXPECT_EQ(m.state_key_prefix(), storage_key);
        auto const clone = m.clone();
        EXPECT_EQ(
            dynamic_cast<TypeParam const &>(*clone).state_key_prefix(),
            storage_key);
        m.up(64);
        EXPECT_EQ(m.state_key_prefix(), account_key);
    }
}

TYPED_TEST(LbtMachineTyped, bulk_and_nibble_walks_record_the_same_key)
{
    auto const ah = keccak256(ADDR_A.bytes);
    auto const sh = keccak256(compute_page_key(SLOT_FAR).bytes);
    for (auto const &section :
         {finalized_nibbles, proposal_prefix(bytes32_t{7})}) {
        auto const deepest = concat(
            NibblesView{section},
            STATE_NIBBLE,
            NibblesView{ah},
            NibblesView{sh});
        NibblesView const all{deepest};
        auto const table_start =
            static_cast<unsigned>(section.nibble_size()) + 1;
        for (unsigned const stop :
             {table_start + 10,
              table_start + 64,
              static_cast<unsigned>(all.nibble_size())}) {
            TypeParam one_by_one;
            walk(one_by_one, all.substr(0, stop));
            TypeParam bulk;
            bulk.down(all.substr(0, stop));
            EXPECT_EQ(bulk.depth, one_by_one.depth) << stop;
            EXPECT_EQ(bulk.state_key_prefix(), one_by_one.state_key_prefix())
                << stop;
            TypeParam split;
            split.down(all.substr(0, table_start + 5));
            split.down(all.substr(table_start + 5, stop - table_start - 5));
            EXPECT_EQ(split.depth, one_by_one.depth) << stop;
            EXPECT_EQ(split.state_key_prefix(), one_by_one.state_key_prefix())
                << stop;
        }
    }
}

TYPED_TEST(LbtMachineTyped, storage_emptied)
{
    auto mpt_db = make_db<TypeParam>();
    TrieDb tdb{mpt_db};
    Account const acct{.nonce = 1};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {ADDR_C,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{SLOT0, {bytes32_t{}, V1}}}}}});
    commit_block(
        mpt_db,
        tdb,
        1,
        StateDeltas{
            {ADDR_C,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{SLOT0, {V1, bytes32_t{}}}}}}});
    EXPECT_EQ(
        tdb.state_root(), expected_state_root(mpt_db, tdb, 1, {{ADDR_C, {}}}));
    EXPECT_EQ(tdb.state_root(), PIN_STORAGE_EMPTIED);
}

TYPED_TEST(LbtMachineTyped, reincarnation_wipes_storage)
{
    auto mpt_db = make_db<TypeParam>();
    TrieDb tdb{mpt_db};
    Account const acct{.nonce = 1};
    Account reincarnated = acct;
    reincarnated.incarnation = Incarnation{1, 0};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {
                     {SLOT0, {bytes32_t{}, V1}},
                     {SLOT_FAR, {bytes32_t{}, V2}}}}}});
    commit_block(
        mpt_db,
        tdb,
        1,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, reincarnated},
                 .storage = {{SLOT2, {bytes32_t{}, V2}}}}}});
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{1, 0}, SLOT0), bytes32_t{});
    EXPECT_EQ(
        tdb.state_root(),
        expected_state_root(
            mpt_db, tdb, 1, {{ADDR_A, {compute_page_key(SLOT2)}}}));
    EXPECT_EQ(tdb.state_root(), PIN_REINCARNATION_WIPES_STORAGE);
}

TYPED_TEST(LbtMachineTyped, erase_lifts_account_and_page_leaves)
{
    auto const addr_of = [](uint64_t i) { return Address{i + 1}; };
    // One slot per page: storage_page_t holds 128 slots.
    auto const slot_of = [](uint64_t i) { return bytes32_t{i << 7}; };
    auto const [x, y, z] = shared_first_nibble(
        [&](uint64_t i) { return keccak256(addr_of(i).bytes); });
    auto const [s, t, u] = shared_first_nibble([&](uint64_t i) {
        return keccak256(compute_page_key(slot_of(i)).bytes);
    });
    Address const kept = addr_of(x);
    Address const erased = addr_of(y);
    Address const other = addr_of(z);
    Account const acct{.nonce = 1};
    auto mpt_db = make_db<TypeParam>();
    TrieDb tdb{mpt_db};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {kept,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{slot_of(s), {bytes32_t{}, V1}},
                      {slot_of(t), {bytes32_t{}, V1}},
                      {slot_of(u), {bytes32_t{}, V1}}}}},
            {erased,
             StateDelta{.account = {std::nullopt, acct}, .storage = {}}},
            {other,
             StateDelta{.account = {std::nullopt, acct}, .storage = {}}}});
    commit_block(
        mpt_db,
        tdb,
        1,
        StateDeltas{
            {kept,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{slot_of(t), {V1, bytes32_t{}}}}}},
            {erased,
             StateDelta{.account = {acct, std::nullopt}, .storage = {}}}});
    EXPECT_EQ(
        tdb.state_root(),
        expected_state_root(
            mpt_db,
            tdb,
            1,
            {{kept,
              {compute_page_key(slot_of(s)), compute_page_key(slot_of(u))}},
             {other, {}}}));
    EXPECT_EQ(tdb.state_root(), PIN_ERASE_LIFTS_ACCOUNT_AND_PAGE);
}

TYPED_TEST(LbtMachineTyped, empty_state_reports_mpt_null_root)
{
    auto mpt_db = make_db<TypeParam>();
    TrieDb tdb{mpt_db};
    Account const acct{.nonce = 1};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{SLOT0, {bytes32_t{}, V1}}}}}});
    EXPECT_NE(tdb.state_root(), NULL_ROOT);
    commit_block(
        mpt_db,
        tdb,
        1,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, std::nullopt},
                 .storage = {{SLOT0, {V1, bytes32_t{}}}}}}});
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);
}

TYPED_TEST(LbtMachineTyped, account_and_slot_updates_in_place)
{
    auto mpt_db = make_db<TypeParam>();
    TrieDb tdb{mpt_db};
    Account const a0{.nonce = 1};
    Account const c0{.nonce = 1};
    std::vector<ExpectedAccount> const expected{
        {ADDR_A, {compute_page_key(SLOT0), compute_page_key(SLOT_FAR)}},
        {ADDR_C, {compute_page_key(SLOT0)}}};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, a0},
                 .storage =
                     {{SLOT0, {bytes32_t{}, V1}},
                      {SLOT1, {bytes32_t{}, V2}},
                      {SLOT_FAR, {bytes32_t{}, V1}}}}},
            {ADDR_C,
             StateDelta{
                 .account = {std::nullopt, c0},
                 .storage = {{SLOT0, {bytes32_t{}, V2}}}}}});
    auto const root0 = tdb.state_root();
    EXPECT_EQ(root0, expected_state_root(mpt_db, tdb, 0, expected));

    Account const a1{.balance = 5, .nonce = 2};
    Account const c1{.balance = 7, .nonce = 1};
    commit_block(
        mpt_db,
        tdb,
        1,
        StateDeltas{
            {ADDR_A, StateDelta{.account = {a0, a1}, .storage = {}}},
            {ADDR_C, StateDelta{.account = {c0, c1}, .storage = {}}}});
    auto const root1 = tdb.state_root();
    EXPECT_NE(root1, root0);
    EXPECT_EQ(root1, expected_state_root(mpt_db, tdb, 1, expected));

    commit_block(
        mpt_db,
        tdb,
        2,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {a1, a1},
                 .storage = {{SLOT1, {V2, V1}}, {SLOT2, {bytes32_t{}, V2}}}}}});
    EXPECT_NE(tdb.state_root(), root1);
    EXPECT_EQ(tdb.state_root(), expected_state_root(mpt_db, tdb, 2, expected));
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{0, 0}, SLOT1), V1);
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{0, 0}, SLOT2), V2);
}

// Two accounts that share their first nibble and nothing else give the State
// table root a single internal child; two pages that do the same give the
// account node one.
TYPED_TEST(LbtMachineTyped, lone_internal_child_under_table_and_account)
{
    auto const addr_of = [](uint64_t i) { return Address{i + 1}; };
    auto const slot_of = [](uint64_t i) { return bytes32_t{i << 7}; };
    auto const [x, y, unused_account] = shared_first_nibble(
        [&](uint64_t i) { return keccak256(addr_of(i).bytes); });
    auto const [s, t, unused_page] = shared_first_nibble([&](uint64_t i) {
        return keccak256(compute_page_key(slot_of(i)).bytes);
    });
    Account const acct{.nonce = 1};
    auto mpt_db = make_db<TypeParam>();
    TrieDb tdb{mpt_db};
    commit_block(
        mpt_db,
        tdb,
        0,
        StateDeltas{
            {addr_of(x),
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{slot_of(s), {bytes32_t{}, V1}},
                      {slot_of(t), {bytes32_t{}, V2}}}}},
            {addr_of(y),
             StateDelta{.account = {std::nullopt, acct}, .storage = {}}}});
    EXPECT_EQ(
        tdb.state_root(),
        expected_state_root(
            mpt_db,
            tdb,
            0,
            {{addr_of(x),
              {compute_page_key(slot_of(s)), compute_page_key(slot_of(t))}},
             {addr_of(y), {}}}));
}
