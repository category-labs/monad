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
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
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
#include <type_traits>
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
    domain_path(mpt::NibblesView const prefix, uint64_t const domain)
    {
        uint8_t domain_bytes[sizeof(uint64_t)];
        intx::be::store(domain_bytes, domain);
        return mpt::concat(
            prefix,
            domain_state_nibbles,
            mpt::NibblesView{to_byte_string_view(domain_bytes)});
    }

    mpt::Nibbles domain_path(uint64_t const domain)
    {
        return domain_path(finalized_nibbles, domain);
    }

    mpt::Nibbles domain_account_path(uint64_t const domain, Address const &addr)
    {
        return mpt::concat(
            domain_path(domain),
            mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})});
    }

    mpt::Nibbles domain_storage_path(
        uint64_t const domain, Address const &addr, bytes32_t const &key)
    {
        return mpt::concat(
            domain_account_path(domain, addr),
            mpt::NibblesView{keccak256({key.bytes, sizeof(key.bytes)})});
    }

    void add_state_delta(
        StateDeltas &state_deltas, Address const &addr, StateDelta delta)
    {
        StateDeltas::accessor it{};
        state_deltas.emplace(it, addr, std::move(delta));
    }

    void add_domain_state_delta(
        DomainStateDeltas &domain_deltas, uint64_t const domain,
        Address const &addr, StateDelta delta)
    {
        DomainStateDeltas::accessor domain_it{};
        domain_deltas.emplace(
            domain_it, domain, std::make_unique<StateDeltas>());
        add_state_delta(*domain_it->second, addr, std::move(delta));
    }

    bytes32_t commit_plain_state_root(
        TrieDb &tdb, StateDeltas const &state_deltas,
        uint64_t const block_number, bytes32_t const &block_id)
    {
        auto builder = make_commit_builder(block_number, tdb);
        builder->add_state_deltas(state_deltas);
        BlockHeader header{.number = block_number};
        tdb.commit(
            block_id, *builder, header, state_deltas, [&](BlockHeader &h) {
                h.state_root = tdb.state_root();
            });
        return tdb.state_root();
    }

    DomainStateRoots commit_domain_state(
        TrieDb &tdb, DomainStateDeltas const &domain_deltas,
        uint64_t const block_number, bytes32_t const &block_id)
    {
        auto builder = make_commit_builder(block_number, tdb);
        builder->add_domain_state_deltas(domain_deltas);
        DomainStateDeltas const *const delta_sets[] = {&domain_deltas};
        return tdb.commit_domain_state_deltas(
            block_id, *builder, delta_sets, block_number, {});
    }

    std::unique_ptr<mpt::StateMachine>
    make_expected_machine(bool const page_encoded)
    {
        if (page_encoded) {
            return std::make_unique<MonadInMemoryMachine>();
        }
        return std::make_unique<InMemoryMachine>();
    }

    void expect_domain_root_node(
        mpt::Db &db, TrieDb &tdb, mpt::NibblesView const prefix,
        uint64_t const domain, bytes32_t const &expected_root,
        uint64_t const block_number)
    {
        auto const res =
            db.find(tdb.get_root(), domain_path(prefix, domain), block_number);
        ASSERT_TRUE(res.has_value());
        auto const data = res.value().node->data();
        ASSERT_EQ(data.size(), sizeof(bytes32_t));
        EXPECT_EQ(to_bytes(data), expected_root);
    }

    void expect_domain_root_node(
        mpt::Db &db, TrieDb &tdb, uint64_t const domain,
        bytes32_t const &expected_root, uint64_t const block_number)
    {
        expect_domain_root_node(
            db, tdb, finalized_nibbles, domain, expected_root, block_number);
    }

    bytes32_t
    root_for_domain(DomainStateRoots const &roots, uint64_t const domain)
    {
        auto const it = std::find_if(
            roots.begin(), roots.end(), [domain](auto const &entry) {
                return entry.first == domain;
            });
        MONAD_ASSERT(it != roots.end());
        return it->second;
    }

    template <typename Machine>
    mpt::Db make_domain_db()
    {
        if constexpr (std::is_base_of_v<OnDiskMachine, Machine>) {
            return mpt::Db{std::make_unique<Machine>(), mpt::OnDiskDbConfig{}};
        }
        else {
            return mpt::Db{std::make_unique<Machine>()};
        }
    }
}

template <typename Machine>
struct DomainWritePathTest : public ::testing::Test
{
    mpt::Db db{make_domain_db<Machine>()};
    TrieDb tdb;

    DomainWritePathTest()
        : tdb{db}
    {
        seed_finalized_block_zero(db, tdb);
    }
};

using DomainMachineTypes = ::testing::Types<
    InMemoryMachine, OnDiskMachine, MonadInMemoryMachine, MonadOnDiskMachine>;
TYPED_TEST_SUITE(DomainWritePathTest, DomainMachineTypes);

TYPED_TEST(DomainWritePathTest, domain_raw_trie_insert)
{
    using namespace mpt;

    constexpr uint64_t domain{0x1111111111111111ULL};
    uint8_t domain_bytes[sizeof(uint64_t)];
    intx::be::store(domain_bytes, domain);
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

    UpdateList domain_list;
    domain_list.push_front(alloc.emplace_back(Update{
        .key = bytes_alloc.emplace_back(domain_bytes, sizeof(domain_bytes)),
        .value = byte_string_view{},
        .next = std::move(inner_list),
        .version = 1}));

    UpdateList state_list;
    state_list.push_front(alloc.emplace_back(Update{
        .key = domain_state_nibbles,
        .value = byte_string_view{},
        .next = std::move(domain_list),
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
        DOMAIN_STATE_NIBBLE,
        NibblesView{to_byte_string_view(domain_bytes)},
        NibblesView{inner_hash});
    auto inner_res = this->db.find(root, inner_key, 1);
    EXPECT_TRUE(inner_res.has_value()) << "inner account not found";
}

TYPED_TEST(DomainWritePathTest, domain_commit_empty_inner_deltas)
{
    constexpr uint64_t domain{0x1212121212121212ULL};
    DomainStateDeltas domain_deltas;
    DomainStateDeltas::accessor domain_it{};
    domain_deltas.emplace(domain_it, domain, std::make_unique<StateDeltas>());
    domain_it.release();

    auto const roots =
        commit_domain_state(this->tdb, domain_deltas, 1, bytes32_t{1});

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, domain);
    EXPECT_EQ(roots[0].second, NULL_ROOT);
}

TYPED_TEST(DomainWritePathTest, domain_transaction_and_receipt_tries)
{
    constexpr uint64_t domain{0x1313131313131313ULL};
    constexpr uint64_t domain2{0x2424242424242424ULL};
    constexpr Address sender{0x1234};
    std::vector<Transaction> const transactions{
        Transaction{.nonce = 7, .gas_limit = 21'000, .to = Address{0x55}},
        Transaction{.nonce = 8, .gas_limit = 22'000, .to = Address{0x66}}};
    std::vector<Address> const senders{sender, Address{0x5678}};
    std::vector<Address> const domain_senders{sender, Address{}};
    std::vector<Receipt> const receipts{
        Receipt{.status = 1, .gas_used = 21'000},
        Receipt{.status = 0, .gas_used = 43'000}};
    DomainStateDeltas empty_state;
    DomainStateDeltas const *const empty_delta_sets[] = {&empty_state};
    std::vector<DomainBlockAncillaries> const domain_blocks{
        DomainBlockAncillaries{
            .domain_id = domain,
            .transactions = transactions,
            .senders = domain_senders,
            .receipts = receipts},
        DomainBlockAncillaries{
            .domain_id = domain2,
            .transactions = transactions,
            .senders = domain_senders,
            .receipts = receipts}};

    this->tdb.set_block_and_prefix(0, {});
    auto builder = make_commit_builder(1, this->tdb);
    builder->add_transactions(transactions, senders)
        .add_receipts(receipts)
        .add_domain_block_ancillaries(domain_blocks);
    auto const roots = this->tdb.commit_domain_state_deltas(
        bytes32_t{1}, *builder, empty_delta_sets, 1, {});
    EXPECT_TRUE(roots.empty());
    this->tdb.finalize(1, bytes32_t{1});

    uint8_t domain_bytes[sizeof(uint64_t)];
    intx::be::store(domain_bytes, domain);
    uint8_t domain2_bytes[sizeof(uint64_t)];
    intx::be::store(domain2_bytes, domain2);

    auto const table_root = [&](unsigned char const table) {
        auto result = this->db.find(
            this->tdb.get_root(), concat(FINALIZED_NIBBLE, table), 1);
        MONAD_ASSERT(result.has_value());
        return byte_string{result.value().node->data()};
    };
    auto const domain_root = [&](unsigned char const table,
                                 uint8_t const *const domain_bytes) {
        auto result = this->db.find(
            this->tdb.get_root(),
            concat(
                FINALIZED_NIBBLE,
                table,
                NibblesView{byte_string_view{domain_bytes, sizeof(uint64_t)}}),
            1);
        MONAD_ASSERT(result.has_value());
        return byte_string{result.value().node->data()};
    };
    EXPECT_EQ(
        domain_root(DOMAIN_TRANSACTION_NIBBLE, domain_bytes),
        table_root(TRANSACTION_NIBBLE));
    EXPECT_EQ(
        domain_root(DOMAIN_TRANSACTION_NIBBLE, domain2_bytes),
        table_root(TRANSACTION_NIBBLE));
    EXPECT_EQ(
        domain_root(DOMAIN_RECEIPT_NIBBLE, domain_bytes),
        table_root(RECEIPT_NIBBLE));
    EXPECT_EQ(
        domain_root(DOMAIN_RECEIPT_NIBBLE, domain2_bytes),
        table_root(RECEIPT_NIBBLE));

    auto const index = rlp::encode_unsigned(0u);
    auto transaction_result = this->db.find(
        this->tdb.get_root(),
        concat(
            FINALIZED_NIBBLE,
            DOMAIN_TRANSACTION_NIBBLE,
            NibblesView{to_byte_string_view(domain_bytes)},
            NibblesView{index}),
        1);
    ASSERT_TRUE(transaction_result.has_value());
    auto transaction_value = transaction_result.value().node->value();
    auto decoded_transaction = decode_transaction_db(transaction_value);
    ASSERT_TRUE(decoded_transaction.has_value());
    EXPECT_EQ(decoded_transaction.value().first, transactions[0]);
    EXPECT_EQ(decoded_transaction.value().second, sender);

    auto const second_index = rlp::encode_unsigned(1u);
    auto second_transaction_result = this->db.find(
        this->tdb.get_root(),
        concat(
            FINALIZED_NIBBLE,
            DOMAIN_TRANSACTION_NIBBLE,
            NibblesView{to_byte_string_view(domain_bytes)},
            NibblesView{second_index}),
        1);
    ASSERT_TRUE(second_transaction_result.has_value());
    auto second_transaction_value =
        second_transaction_result.value().node->value();
    auto second_decoded_transaction =
        decode_transaction_db(second_transaction_value);
    ASSERT_TRUE(second_decoded_transaction.has_value());
    EXPECT_EQ(second_decoded_transaction.value().first, transactions[1]);
    EXPECT_EQ(second_decoded_transaction.value().second, Address{});

    auto const transaction_hash =
        keccak256(rlp::encode_transaction(transactions[0]));
    auto hash_result = this->db.find(
        this->tdb.get_root(),
        concat(
            FINALIZED_NIBBLE,
            DOMAIN_TX_HASH_NIBBLE,
            NibblesView{to_byte_string_view(domain_bytes)},
            NibblesView{transaction_hash}),
        1);
    ASSERT_TRUE(hash_result.has_value());
    auto hash_value = hash_result.value().node->value();
    auto location = decode_transaction_location_db(hash_value);
    ASSERT_TRUE(location.has_value());
    EXPECT_EQ(location.value(), (std::pair<uint64_t, uint32_t>{1, 0}));
    auto domain2_hash_result = this->db.find(
        this->tdb.get_root(),
        concat(
            FINALIZED_NIBBLE,
            DOMAIN_TX_HASH_NIBBLE,
            NibblesView{to_byte_string_view(domain2_bytes)},
            NibblesView{transaction_hash}),
        1);
    ASSERT_TRUE(domain2_hash_result.has_value());
    auto domain2_hash_value = domain2_hash_result.value().node->value();
    auto domain2_location = decode_transaction_location_db(domain2_hash_value);
    ASSERT_TRUE(domain2_location.has_value());
    EXPECT_EQ(domain2_location.value(), (std::pair<uint64_t, uint32_t>{1, 0}));

    auto receipt_result = this->db.find(
        this->tdb.get_root(),
        concat(
            FINALIZED_NIBBLE,
            DOMAIN_RECEIPT_NIBBLE,
            NibblesView{to_byte_string_view(domain_bytes)},
            NibblesView{index}),
        1);
    ASSERT_TRUE(receipt_result.has_value());
    auto receipt_value = receipt_result.value().node->value();
    auto decoded_receipt = decode_receipt_db(receipt_value);
    ASSERT_TRUE(decoded_receipt.has_value());
    EXPECT_EQ(decoded_receipt.value().first, receipts[0]);

    this->tdb.set_block_and_prefix(1, {});
    auto second_builder = make_commit_builder(2, this->tdb);
    std::vector<DomainBlockAncillaries> const second_blocks{
        DomainBlockAncillaries{
            .domain_id = domain2,
            .transactions = transactions,
            .senders = domain_senders,
            .receipts = receipts}};
    second_builder->add_domain_block_ancillaries(second_blocks);
    this->tdb.commit_domain_state_deltas(
        bytes32_t{2}, *second_builder, empty_delta_sets, 2, {});
    this->tdb.finalize(2, bytes32_t{2});
    EXPECT_TRUE(this->db
                    .find(
                        this->tdb.get_root(),
                        concat(
                            FINALIZED_NIBBLE,
                            DOMAIN_TRANSACTION_NIBBLE,
                            NibblesView{to_byte_string_view(domain_bytes)},
                            NibblesView{index}),
                        2)
                    .has_error());
    EXPECT_TRUE(this->db
                    .find(
                        this->tdb.get_root(),
                        concat(
                            FINALIZED_NIBBLE,
                            DOMAIN_TRANSACTION_NIBBLE,
                            NibblesView{to_byte_string_view(domain2_bytes)},
                            NibblesView{index}),
                        2)
                    .has_value());

    this->tdb.set_block_and_prefix(2, {});
    auto empty_builder = make_commit_builder(3, this->tdb);
    empty_builder->add_domain_block_ancillaries(
        std::span<DomainBlockAncillaries const>{});
    this->tdb.commit_domain_state_deltas(
        bytes32_t{3}, *empty_builder, empty_delta_sets, 3, {});
    this->tdb.finalize(3, bytes32_t{3});
    EXPECT_TRUE(this->db
                    .find(
                        this->tdb.get_root(),
                        concat(
                            FINALIZED_NIBBLE,
                            DOMAIN_RECEIPT_NIBBLE,
                            NibblesView{to_byte_string_view(domain2_bytes)},
                            NibblesView{index}),
                        3)
                    .has_error());
    EXPECT_TRUE(this->db
                    .find(
                        this->tdb.get_root(),
                        concat(
                            FINALIZED_NIBBLE,
                            DOMAIN_RECEIPT_NIBBLE,
                            NibblesView{to_byte_string_view(domain_bytes)},
                            NibblesView{index}),
                        3)
                    .has_error());
    auto persistent_hash_result = this->db.find(
        this->tdb.get_root(),
        concat(
            FINALIZED_NIBBLE,
            DOMAIN_TX_HASH_NIBBLE,
            NibblesView{to_byte_string_view(domain_bytes)},
            NibblesView{transaction_hash}),
        3);
    ASSERT_TRUE(persistent_hash_result.has_value());
    auto persistent_hash_value = persistent_hash_result.value().node->value();
    auto persistent_location =
        decode_transaction_location_db(persistent_hash_value);
    ASSERT_TRUE(persistent_location.has_value());
    EXPECT_EQ(
        persistent_location.value(), (std::pair<uint64_t, uint32_t>{1, 0}));
}

TYPED_TEST(DomainWritePathTest, domain_commit_account_root_matches_plain_state)
{
    constexpr uint64_t domain{0x2222222222222222ULL};
    StateDeltas inner;
    StateDelta const delta{
        .account = {std::nullopt, Account{.balance = 42}}, .storage = {}};
    add_state_delta(inner, ADDR_A, delta);

    mpt::Db expected_db{make_expected_machine(this->tdb.is_page_encoded())};
    TrieDb expected_tdb{expected_db};
    auto const expected_root =
        commit_plain_state_root(expected_tdb, inner, 1, bytes32_t{1});

    DomainStateDeltas domain_deltas;
    add_domain_state_delta(domain_deltas, domain, ADDR_A, delta);
    auto const roots =
        commit_domain_state(this->tdb, domain_deltas, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, domain);
    EXPECT_EQ(roots[0].second, expected_root);
    expect_domain_root_node(this->db, this->tdb, domain, expected_root, 1);

    auto const account_res = this->db.find(
        this->tdb.get_root(), domain_account_path(domain, ADDR_A), 1);
    ASSERT_TRUE(account_res.has_value());
    auto encoded_account = account_res.value().node->value();
    auto const decoded = decode_account_db_ignore_address(encoded_account);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(decoded.value().balance, 42);
}

TYPED_TEST(DomainWritePathTest, domain_commit_storage_root_matches_plain_state)
{
    constexpr uint64_t domain{0x3333333333333333ULL};
    Account const account{.balance = 100};
    StateDeltas inner;
    StateDelta const delta{
        .account = {std::nullopt, account},
        .storage = {{key1, {bytes32_t{}, value1}}}};
    add_state_delta(inner, ADDR_A, delta);

    mpt::Db expected_db{make_expected_machine(this->tdb.is_page_encoded())};
    TrieDb expected_tdb{expected_db};
    auto const expected_root =
        commit_plain_state_root(expected_tdb, inner, 1, bytes32_t{1});

    DomainStateDeltas domain_deltas;
    add_domain_state_delta(domain_deltas, domain, ADDR_A, delta);
    auto const roots =
        commit_domain_state(this->tdb, domain_deltas, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].first, domain);
    EXPECT_EQ(roots[0].second, expected_root);
    expect_domain_root_node(this->db, this->tdb, domain, expected_root, 1);

    auto const storage_key =
        this->tdb.is_page_encoded() ? compute_page_key(key1) : key1;
    auto const storage_res = this->db.find(
        this->tdb.get_root(),
        domain_storage_path(domain, ADDR_A, storage_key),
        1);
    ASSERT_TRUE(storage_res.has_value());
    auto encoded_storage = storage_res.value().node->value();
    auto const decoded = decode_storage_db_raw(encoded_storage);
    ASSERT_TRUE(decoded.has_value());
    EXPECT_EQ(to_bytes(decoded.value().first), storage_key);
    if (this->tdb.is_page_encoded()) {
        auto const page = decode_storage_page(decoded.value().second);
        ASSERT_TRUE(page.has_value());
        EXPECT_EQ(page.value()[compute_slot_offset(key1)], value1);
    }
    else {
        EXPECT_EQ(to_bytes(decoded.value().second), value1);
    }
}

TYPED_TEST(DomainWritePathTest, domain_commit_multiple_domains)
{
    constexpr uint64_t domain_1{0x5151515151515151ULL};
    constexpr uint64_t domain_2{0x5252525252525252ULL};
    StateDelta const delta1{
        .account = {std::nullopt, Account{.balance = 111}}, .storage = {}};
    StateDelta const delta2{
        .account = {std::nullopt, Account{.balance = 222}}, .storage = {}};

    StateDeltas inner1;
    add_state_delta(inner1, ADDR_A, delta1);
    mpt::Db expected_db1{make_expected_machine(this->tdb.is_page_encoded())};
    TrieDb expected_tdb1{expected_db1};
    auto const expected_root1 =
        commit_plain_state_root(expected_tdb1, inner1, 1, bytes32_t{1});

    StateDeltas inner2;
    add_state_delta(inner2, ADDR_B, delta2);
    mpt::Db expected_db2{make_expected_machine(this->tdb.is_page_encoded())};
    TrieDb expected_tdb2{expected_db2};
    auto const expected_root2 =
        commit_plain_state_root(expected_tdb2, inner2, 1, bytes32_t{1});

    DomainStateDeltas domain_deltas;
    add_domain_state_delta(domain_deltas, domain_1, ADDR_A, delta1);
    add_domain_state_delta(domain_deltas, domain_2, ADDR_B, delta2);
    auto const roots =
        commit_domain_state(this->tdb, domain_deltas, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);

    ASSERT_EQ(roots.size(), 2);
    EXPECT_EQ(root_for_domain(roots, domain_1), expected_root1);
    EXPECT_EQ(root_for_domain(roots, domain_2), expected_root2);
    expect_domain_root_node(this->db, this->tdb, domain_1, expected_root1, 1);
    expect_domain_root_node(this->db, this->tdb, domain_2, expected_root2, 1);
}

TYPED_TEST(DomainWritePathTest, domain_commit_root_changes_across_writes)
{
    constexpr uint64_t domain{0x4444444444444444ULL};
    mpt::Db expected_db{make_expected_machine(this->tdb.is_page_encoded())};
    TrieDb expected_tdb{expected_db};

    StateDeltas inner_1;
    StateDelta const delta_1{
        .account = {std::nullopt, Account{.balance = 10}}, .storage = {}};
    add_state_delta(inner_1, ADDR_A, delta_1);
    auto const expected_root_1 =
        commit_plain_state_root(expected_tdb, inner_1, 1, bytes32_t{1});

    DomainStateDeltas domain_deltas_1;
    add_domain_state_delta(domain_deltas_1, domain, ADDR_A, delta_1);
    auto const roots_1 =
        commit_domain_state(this->tdb, domain_deltas_1, 1, bytes32_t{1});
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

    DomainStateDeltas domain_deltas_2;
    add_domain_state_delta(domain_deltas_2, domain, ADDR_A, delta_2);
    auto const roots_2 =
        commit_domain_state(this->tdb, domain_deltas_2, 2, bytes32_t{2});
    this->tdb.finalize(2, bytes32_t{2});
    this->tdb.set_block_and_prefix(2);
    ASSERT_EQ(roots_2.size(), 1);
    EXPECT_EQ(roots_2[0].second, expected_root_2);
    EXPECT_NE(roots_1[0].second, roots_2[0].second);
    expect_domain_root_node(this->db, this->tdb, domain, expected_root_2, 2);
}

TYPED_TEST(
    DomainWritePathTest,
    domain_commit_preserves_unchanged_slots_in_existing_page)
{
    if (!this->tdb.is_page_encoded()) {
        GTEST_SKIP() << "test requires page-encoded storage";
    }

    // A second write to a domain page must load the existing page from the
    // domain trie. Seed two slots on one page, update one, and verify the
    // untouched slot is preserved.
    constexpr uint64_t domain{0x5454545454545454ULL};
    auto const adjacent_key = compute_slot_key(
        compute_page_key(key1),
        static_cast<uint8_t>(compute_slot_offset(key1) + 1));
    bytes32_t const updated_value{9};
    Account const account{.balance = 100};

    mpt::Db expected_db{std::make_unique<MonadInMemoryMachine>()};
    TrieDb expected_tdb{expected_db};

    StateDelta const initial_delta{
        .account = {std::nullopt, account},
        .storage = {
            {key1, {bytes32_t{}, value1}},
            {adjacent_key, {bytes32_t{}, value2}}}};
    StateDeltas initial_state;
    add_state_delta(initial_state, ADDR_A, initial_delta);
    commit_plain_state_root(expected_tdb, initial_state, 1, bytes32_t{1});

    DomainStateDeltas initial_domain_state;
    add_domain_state_delta(initial_domain_state, domain, ADDR_A, initial_delta);
    commit_domain_state(this->tdb, initial_domain_state, 1, bytes32_t{1});
    this->tdb.finalize(1, bytes32_t{1});
    this->tdb.set_block_and_prefix(1);

    StateDelta const update_delta{
        .account = {account, account},
        .storage = {{key1, {value1, updated_value}}}};
    StateDeltas update_state;
    add_state_delta(update_state, ADDR_A, update_delta);
    auto const expected_root =
        commit_plain_state_root(expected_tdb, update_state, 2, bytes32_t{2});

    DomainStateDeltas update_domain_state;
    add_domain_state_delta(update_domain_state, domain, ADDR_A, update_delta);
    auto const roots =
        commit_domain_state(this->tdb, update_domain_state, 2, bytes32_t{2});
    this->tdb.finalize(2, bytes32_t{2});
    this->tdb.set_block_and_prefix(2);

    ASSERT_EQ(roots.size(), 1);
    EXPECT_EQ(roots[0].second, expected_root);

    auto const page_key = compute_page_key(key1);
    auto const storage_res = this->db.find(
        this->tdb.get_root(), domain_storage_path(domain, ADDR_A, page_key), 2);
    ASSERT_TRUE(storage_res.has_value());
    auto encoded_storage = storage_res.value().node->value();
    auto const decoded = decode_storage_db_raw(encoded_storage);
    ASSERT_TRUE(decoded.has_value());
    ASSERT_EQ(to_bytes(decoded.value().first), page_key);
    auto const page = decode_storage_page(decoded.value().second);
    ASSERT_TRUE(page.has_value());
    EXPECT_EQ(page.value()[compute_slot_offset(key1)], updated_value);
    EXPECT_EQ(page.value()[compute_slot_offset(adjacent_key)], value2);
}

TEST_F(OnDiskTrieDbWithFileFixture, domain_reads_and_merge)
{
    constexpr uint64_t domain_1{0x1111111111111111ULL};
    constexpr uint64_t domain_2{0x2222222222222222ULL};
    Account const account_1{.balance = 111};
    Account const account_2{.balance = 222};

    TrieDb tdb{this->db};
    seed_finalized_block_zero(this->db, tdb);
    DomainStateDeltas domain_deltas;
    add_domain_state_delta(
        domain_deltas,
        domain_1,
        ADDR_A,
        StateDelta{
            .account = {std::nullopt, account_1},
            .storage = {{key1, {bytes32_t{}, value1}}}});
    add_domain_state_delta(
        domain_deltas,
        domain_2,
        ADDR_A,
        StateDelta{
            .account = {std::nullopt, account_2},
            .storage = {{key1, {bytes32_t{}, value2}}}});
    commit_domain_state(tdb, domain_deltas, 1, bytes32_t{1});
    tdb.finalize(1, bytes32_t{1});
    tdb.set_block_and_prefix(1);

    EXPECT_EQ(tdb.read_account(ADDR_A), std::nullopt);
    EXPECT_EQ(tdb.read_account(ADDR_A, domain_1), account_1);
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_1), value1);
    EXPECT_EQ(tdb.read_account(ADDR_A, domain_2), account_2);
    EXPECT_EQ(
        tdb.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_2), value2);

    vm::VM vm;
    BlockState block_state{tdb, vm};
    EXPECT_EQ(block_state.read_account(ADDR_A, domain_1), account_1);
    EXPECT_EQ(
        block_state.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_1),
        value1);
    EXPECT_EQ(block_state.read_account(ADDR_A, domain_2), account_2);
    EXPECT_EQ(
        block_state.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_2),
        value2);

    State state_1{block_state, Incarnation{1, 1}, false, domain_1};
    State state_2{block_state, Incarnation{1, 2}, false, domain_2};
    State stale_state_1{block_state, Incarnation{1, 3}, false, domain_1};
    EXPECT_EQ(state_1.get_balance(ADDR_A), account_1.balance);
    EXPECT_EQ(state_1.get_storage(ADDR_A, key1), value1);
    EXPECT_EQ(state_2.get_balance(ADDR_A), account_2.balance);
    EXPECT_EQ(state_2.get_storage(ADDR_A, key1), value2);
    EXPECT_EQ(stale_state_1.get_balance(ADDR_A), account_1.balance);
    EXPECT_EQ(stale_state_1.get_storage(ADDR_A, key1), value1);

    mpt::RODb rodb{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {this->dbname}}};
    TrieRODb trie_ro{rodb};
    trie_ro.set_block_and_prefix(1);
    EXPECT_EQ(
        trie_ro.domain_state_root(domain_1), tdb.domain_state_root(domain_1));
    EXPECT_EQ(
        trie_ro.domain_state_root(domain_2), tdb.domain_state_root(domain_2));
    EXPECT_EQ(trie_ro.domain_state_root(0), NULL_ROOT);
    EXPECT_EQ(trie_ro.read_account(ADDR_A, domain_1), account_1);
    EXPECT_EQ(
        trie_ro.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_1),
        value1);
    EXPECT_EQ(trie_ro.read_account(ADDR_A, domain_2), account_2);
    EXPECT_EQ(
        trie_ro.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_2),
        value2);

    state_1.add_to_balance(ADDR_A, 10);
    EXPECT_EQ(state_1.set_storage(ADDR_A, key1, value2), EVMC_STORAGE_MODIFIED);
    EXPECT_TRUE(block_state.can_merge(state_1));
    block_state.merge(state_1);
    EXPECT_EQ(
        block_state.read_account(ADDR_A, domain_1)->balance,
        account_1.balance + 10);
    EXPECT_EQ(
        block_state.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_1),
        value2);
    EXPECT_EQ(block_state.read_account(ADDR_A, domain_2), account_2);
    EXPECT_EQ(
        block_state.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_2),
        value2);
    EXPECT_EQ(block_state.read_account(ADDR_A), std::nullopt);
    EXPECT_FALSE(block_state.can_merge(stale_state_1));

    state_2.add_to_balance(ADDR_A, 20);
    EXPECT_EQ(state_2.set_storage(ADDR_A, key1, value1), EVMC_STORAGE_MODIFIED);
    EXPECT_TRUE(block_state.can_merge(state_2));
    block_state.merge(state_2);
    EXPECT_EQ(
        block_state.read_account(ADDR_A, domain_2)->balance,
        account_2.balance + 20);
    EXPECT_EQ(
        block_state.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_2),
        value1);
    EXPECT_EQ(
        block_state.read_account(ADDR_A, domain_1)->balance,
        account_1.balance + 10);
    EXPECT_EQ(
        block_state.read_storage(ADDR_A, Incarnation{0, 0}, key1, domain_1),
        value2);
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
