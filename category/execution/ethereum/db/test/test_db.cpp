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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex_literal.hpp>
#include <category/core/keccak.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/traverse_util.hpp>

#include <ethash/keccak.hpp>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>
#include <intx/intx.hpp>
#include <nlohmann/json_fwd.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <iostream>
#include <memory>

#include <test_resource_data.h>

#include <algorithm>
#include <bit>
#include <cstdint>
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

namespace
{
    // clang-format off
    auto const STRESS_TEST_CODE =
        evmc::from_hex("0x5b61c3506080511015603f576000600061c3506000600173aaaf5374fce5edbc8e2a8697c15331677e6ebf0b610640f16000556001608051016080526000565b60805160015500")
            .value();
    // clang-format on
    auto const STRESS_TEST_CODE_HASH = to_bytes(keccak256(STRESS_TEST_CODE));
    auto const STRESS_TEST_ICODE = vm::make_shared_intercode(STRESS_TEST_CODE);

    auto const REFUND_TEST_CODE =
        evmc::from_hex("0x6000600155600060025560006003556000600455600060055500")
            .value();
    auto const REFUND_TEST_CODE_HASH = to_bytes(keccak256(REFUND_TEST_CODE));
    auto const REFUND_TEST_ICODE = vm::make_shared_intercode(REFUND_TEST_CODE);

    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto value1 =
        0x0000000000000013370000000000000000000000000000000000000000000003_bytes32;
    constexpr auto value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;

    struct ShanghaiEthereumMainnet : EthereumMainnet
    {
        virtual evmc_revision get_revision(
            uint64_t /* block_number */,
            uint64_t /* timestamp */) const override
        {
            return EVMC_SHANGHAI;
        }
    };

    struct InMemoryTrieDbFixture : public ::testing::Test
    {
        static constexpr bool on_disk = false;

        InMemoryMachine machine;
        mpt::Db db{machine};
        vm::VM vm;
    };

    struct OnDiskTrieDbFixture : public ::testing::Test
    {
        static constexpr bool on_disk = true;

        OnDiskMachine machine;
        mpt::Db db{machine, mpt::OnDiskDbConfig{}};
        vm::VM vm;
    };

    ///////////////////////////////////////////
    // DB Getters
    ///////////////////////////////////////////
    std::vector<CallFrame> read_call_frame(
        mpt::Db &db, uint64_t const block_number, uint64_t const txn_idx)
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
        db.traverse(db.root(), machine, block_number);
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
        mpt::Db const &db, uint64_t const block_number, Address const &addr,
        bytes32_t const &key)
    {
        auto const value = db.get(
            mpt::concat(
                FINALIZED_NIBBLE,
                STATE_NIBBLE,
                mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
                mpt::NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
            block_number);
        if (!value.has_value()) {
            return {};
        }
        auto encoded_storage = value.value();
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

TEST(DBTest, read_only)
{
    auto const name =
        std::filesystem::temp_directory_path() /
        (::testing::UnitTest::GetInstance()->current_test_info()->name() +
         std::to_string(rand()));
    {
        OnDiskMachine machine;
        mpt::Db db{machine, mpt::OnDiskDbConfig{.dbname_paths = {name}}};
        TrieDb rw(db);

        Account const acct1{.nonce = 1};
        commit_sequential(
            rw,
            StateDeltas{
                {ADDR_A,
                 StateDelta{.account = {std::nullopt, acct1}, .storage = {}}}},
            Code{},
            BlockHeader{.number = 0});
        Account const acct2{.nonce = 2};
        commit_sequential(
            rw,
            StateDeltas{
                {ADDR_A, StateDelta{.account = {acct1, acct2}, .storage = {}}}},
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
            StateDeltas{
                {ADDR_A, StateDelta{.account = {acct2, acct3}, .storage = {}}}},
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
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{},
        BlockHeader{});

    // Existing storage
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{0, 0}, key1), value1);
    EXPECT_EQ(
        read_storage_and_slot(this->db, tdb.get_block_number(), ADDR_A, key1)
            .first,
        key1);

    // Non-existing key
    EXPECT_EQ(tdb.read_storage(ADDR_A, Incarnation{0, 0}, key2), bytes32_t{});
    EXPECT_EQ(
        read_storage_and_slot(this->db, tdb.get_block_number(), ADDR_A, key2)
            .first,
        bytes32_t{});

    // Non-existing account
    EXPECT_FALSE(tdb.read_account(ADDR_B).has_value());
    EXPECT_EQ(tdb.read_storage(ADDR_B, Incarnation{0, 0}, key1), bytes32_t{});
    EXPECT_EQ(
        read_storage_and_slot(this->db, tdb.get_block_number(), ADDR_B, key1)
            .first,
        bytes32_t{});
}

TYPED_TEST(DBTest, read_code)
{
    Account acct_a{.balance = 1, .code_hash = A_CODE_HASH, .nonce = 1};
    TrieDb tdb{this->db};
    commit_sequential(
        tdb,
        StateDeltas{{ADDR_A, StateDelta{.account = {std::nullopt, acct_a}}}},
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    auto const a_icode = tdb.read_code(A_CODE_HASH);
    EXPECT_EQ(byte_string_view(a_icode->code(), a_icode->size()), A_CODE);

    Account acct_b{.balance = 0, .code_hash = B_CODE_HASH, .nonce = 1};
    commit_sequential(
        tdb,
        StateDeltas{{ADDR_B, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{B_CODE_HASH, B_ICODE}},
        BlockHeader{.number = 1});

    auto const b_icode = tdb.read_code(B_CODE_HASH);
    EXPECT_EQ(byte_string_view(b_icode->code(), b_icode->size()), B_CODE);
}

TEST_F(OnDiskTrieDbFixture, get_proposal_block_ids)
{
    TrieDb tdb{db};
    load_header(db, BlockHeader{.number = 8});
    EXPECT_TRUE(get_proposal_block_ids(db, 8).empty());

    tdb.set_block_and_prefix(8);
    auto const round9_block_id =
        commit_sequential(tdb, StateDeltas{}, Code{}, BlockHeader{.number = 9});
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
    tdb.commit(StateDeltas{}, Code{}, block_id0, header0);
    {
        auto const proposals = get_proposal_block_ids(db, 10);
        EXPECT_EQ(std::set(proposals.begin(), proposals.end()), block_ids);
    }
    tdb.set_block_and_prefix(9);
    BlockHeader const header1{.number = 10};
    bytes32_t const block_id1{header1.number};
    block_ids.emplace(block_id1);
    tdb.commit(StateDeltas{}, Code{}, block_id1, header1);
    {
        auto const proposals = get_proposal_block_ids(db, 10);
        EXPECT_EQ(std::set(proposals.begin(), proposals.end()), block_ids);
    }

    tdb.set_block_and_prefix(9);
    BlockHeader const header2{.number = 10};
    bytes32_t const block_id2{header2.number};
    block_ids.emplace(block_id2);
    tdb.commit(StateDeltas{}, Code{}, block_id2, header2);

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
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{.number = 0});

    acct = tdb.read_account(ADDR_A).value();
    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{key2, {value2, value1}}}}}},
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
        StateDeltas{
            {ADDR_A, StateDelta{.account = {std::nullopt, std::nullopt}}}},
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
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{.number = 0});

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, std::nullopt},
                 .storage =
                     {{key1, {value1, value2}}, {key2, {value2, value1}}}}}},
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
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{},
        BlockHeader{.number = 0});

    acct = tdb.read_account(ADDR_A).value();
    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{key1, {value1, bytes32_t{}}}}}}},
        Code{},
        BlockHeader{.number = 1});

    EXPECT_EQ(
        tdb.state_root(),
        0x1f54a52a44ffa5b8298f7ed596dea62455816e784dce02d79ea583f3a4146598_bytes32);
}

TYPED_TEST(DBTest, commit_receipts_transactions)
{
    using namespace intx;
    using namespace evmc::literals;

    TrieDb tdb{this->db};
    // empty receipts
    commit_sequential(tdb, StateDeltas{}, Code{}, BlockHeader{});
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
        .data = from_hex("0x000000000000000000000000000000000000000000000000000"
                         "000000000000000000000000000000000000043b2126e7a22e0c2"
                         "88dfb469e3de4d2c097f3ca000000000000000000000000000000"
                         "0000000000000000001195387bce41fd499000000000000000000"
                         "0000000000000000000000000000000000000000000000"),
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
        .sc = {.r = r, .s = s}, // no chain_id in legacy transactions
        .nonce = 9,
        .max_fee_per_gas = price,
        .gas_limit = 21'000,
        .value = value};
    Transaction t2{
        .sc = {.r = r, .s = s, .chain_id = 5}, // Goerli
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
        StateDeltas{},
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
            auto res = this->db.get(
                mpt::concat(
                    FINALIZED_NIBBLE,
                    RECEIPT_NIBBLE,
                    mpt::NibblesView{rlp::encode_unsigned<unsigned>(i)}),
                block_id);
            ASSERT_TRUE(res.has_value());
            auto const decode_res = decode_receipt_db(res.value());
            ASSERT_TRUE(decode_res.has_value());
            auto const [receipt, log_index_begin] = decode_res.value();
            EXPECT_EQ(receipt, receipts[i]) << i;
            EXPECT_EQ(log_index_begin, log_i);
            log_i += receipt.logs.size();
        }
    };

    auto verify_read_and_parse_transaction = [&](uint64_t const block_id) {
        for (unsigned i = 0; i < transactions.size(); ++i) {
            auto res = this->db.get(
                mpt::concat(
                    FINALIZED_NIBBLE,
                    TRANSACTION_NIBBLE,
                    mpt::NibblesView{rlp::encode_unsigned<unsigned>(i)}),
                block_id);
            ASSERT_TRUE(res.has_value());
            auto const decode_res = decode_transaction_db(res.value());
            ASSERT_TRUE(decode_res.has_value());
            auto const [tx, sender] = decode_res.value();
            EXPECT_EQ(tx, transactions[i]) << i;
            EXPECT_EQ(sender, senders[i]) << i;
        }
    };
    auto verify_tx_hash = [&](hash256 const &tx_hash,
                              uint64_t const block_id,
                              unsigned const tx_idx) {
        auto const res = this->db.get(
            concat(FINALIZED_NIBBLE, TX_HASH_NIBBLE, mpt::NibblesView{tx_hash}),
            this->db.get_latest_version());
        EXPECT_TRUE(res.has_value());
        EXPECT_EQ(
            res.value(),
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
        StateDeltas{},
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
                this->machine, mpt::OnDiskDbConfig{.dbname_paths = {dbname}}};
        }
        return mpt::Db{this->machine};
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
    load_from_binary(this->db, accounts, code);
    TrieDb tdb{this->db};
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
        StateDeltas{},
        Code{},
        BlockHeader{},
        receipts,
        call_frames,
        senders,
        transactions);

    for (uint64_t txn = 0; txn < NUM_TXNS; ++txn) {
        auto const &res =
            read_call_frame(this->db, tdb.get_block_number(), txn);
        ASSERT_TRUE(!res.empty());
        ASSERT_TRUE(res.size() == 2);
        EXPECT_EQ(res[0], call_frame1);
        EXPECT_EQ(res[1], call_frame2);
    }
}

// test referenced from :
// https://github.com/ethereum/tests/blob/develop/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/Call50000.json
TYPED_TEST(DBTest, call_frames_stress_test)
{
    using namespace intx;

    TrieDb tdb{this->db};

    auto const from = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    auto const to = 0xbbbf5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    auto const ca = 0xaaaf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xffffffffffffffffffffffffffffffff_u128,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {to,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x0fffffffffffff,
                          .code_hash = STRESS_TEST_CODE_HASH}}}},
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0x1b58, .code_hash = NULL_HASH}}}}},
        Code{{STRESS_TEST_CODE_HASH, STRESS_TEST_ICODE}},
        BlockHeader{.number = 0});

    // clang-format off
    byte_string const block_rlp = evmc::from_hex("0xf90283f90219a0d2472bbb9c83b0e7615b791409c2efaccd5cb7d923741bbc44783bf0d063f5b6a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d4934794b94f5374fce5edbc8e2a8697c15331677e6ebf0ba0644bb1009c2332d1532062fe9c28cae87169ccaab2624aa0cfb4f0a0e59ac3aaa0cc2a2a77bb0d7a07b12d7e1d13b9f5dfff4f4bc53052b126e318f8b27b7ab8f9a027408083641cf20cfde86cd87cd57bf10c741d7553352ca96118e31ab8ceb9ceb901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080018433428f00840ee6b2808203e800a000000000000000000000000000000000000000000000000000000000000200008800000000000000000aa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421f863f861800a840ee6b28094bbbf5374fce5edbc8e2a8697c15331677e6ebf0b0a801ba0462186579a4be0ad8a63224059a11693b4c0684b9939f6c2394d1fbe045275f2a059d73f99e037295a5f8c0e656acdb5c8b9acd28ec73c320c277df61f2e2d54f9c0c0")
            .value();
    // clang-format on
    byte_string_view block_rlp_view{block_rlp};
    auto block = rlp::decode_block(block_rlp_view);
    ASSERT_TRUE(!block.has_error());

    BlockHashBufferFinalized block_hash_buffer;
    block_hash_buffer.set(
        block.value().header.number - 1, block.value().header.parent_hash);

    BlockState bs(tdb, this->vm);
    BlockMetrics metrics;

    fiber::PriorityPool pool{1, 1};

    auto const recovered_senders =
        recover_senders(block.value().transactions, pool);
    std::vector<Address> senders(block.value().transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        MONAD_ASSERT(recovered_senders[i].has_value());
        senders[i] = recovered_senders[i].value();
    }
    auto const recovered_authorities =
        recover_authorities(block.value().transactions, pool);
    std::vector<std::vector<CallFrame>> call_frames(
        block.value().transactions.size());
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
    for (size_t i = 0; i < block.value().transactions.size(); ++i) {
        call_tracers.emplace_back(std::make_unique<CallTracer>(
            block.value().transactions[i], call_frames[i]));
    }

    auto const receipts = execute_block<EVMC_SHANGHAI>(
        EthereumMainnet{},
        block.value(),
        senders,
        recovered_authorities,
        bs,
        block_hash_buffer,
        pool,
        metrics,
        call_tracers);

    ASSERT_TRUE(!receipts.has_error());

    bs.log_debug();

    auto const &transactions = block.value().transactions;
    BlockHeader const header{.number = 1};
    bytes32_t const block_id{header.number};
    bs.commit(
        block_id,
        header,
        receipts.value(),
        call_frames,
        recover_senders(transactions),
        transactions,
        {},
        {});
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);

    auto const actual_call_frames =
        read_call_frame(this->db, tdb.get_block_number(), 0);

    EXPECT_EQ(actual_call_frames.size(), 35799);
}

// This test is based on the test `DBTest.call_frames_stress_test`
TYPED_TEST(DBTest, assertion_exception)
{
    using namespace intx;

    TrieDb tdb{this->db};

    auto const from = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    auto const to = 0xbbbf5374fce5edbc8e2a8697c15331677e6ebf0b_address;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {to,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = std::numeric_limits<uint256_t>::max(),
                          .code_hash = STRESS_TEST_CODE_HASH}}}}},
        Code{},
        BlockHeader{.number = 0});

    // clang-format off
    byte_string const block_rlp = evmc::from_hex("0xf90283f90219a0d2472bbb9c83b0e7615b791409c2efaccd5cb7d923741bbc44783bf0d063f5b6a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d4934794b94f5374fce5edbc8e2a8697c15331677e6ebf0ba0644bb1009c2332d1532062fe9c28cae87169ccaab2624aa0cfb4f0a0e59ac3aaa0cc2a2a77bb0d7a07b12d7e1d13b9f5dfff4f4bc53052b126e318f8b27b7ab8f9a027408083641cf20cfde86cd87cd57bf10c741d7553352ca96118e31ab8ceb9ceb901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080018433428f00840ee6b2808203e800a000000000000000000000000000000000000000000000000000000000000200008800000000000000000aa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421f863f861800a840ee6b28094bbbf5374fce5edbc8e2a8697c15331677e6ebf0b0a801ba0462186579a4be0ad8a63224059a11693b4c0684b9939f6c2394d1fbe045275f2a059d73f99e037295a5f8c0e656acdb5c8b9acd28ec73c320c277df61f2e2d54f9c0c0")
            .value();
    // clang-format on

    byte_string_view block_rlp_view{block_rlp};
    auto block = rlp::decode_block(block_rlp_view);
    ASSERT_TRUE(!block.has_error());

    BlockHashBufferFinalized block_hash_buffer;
    block_hash_buffer.set(
        block.value().header.number - 1, block.value().header.parent_hash);

    BlockState bs(tdb, this->vm);
    BlockMetrics metrics;

    fiber::PriorityPool pool{1, 1};

    auto const recovered_senders =
        recover_senders(block.value().transactions, pool);
    std::vector<Address> senders(block.value().transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        MONAD_ASSERT(recovered_senders[i].has_value());
        senders[i] = recovered_senders[i].value();
    }
    auto const recovered_authorities =
        recover_authorities(block.value().transactions, pool);
    std::vector<std::vector<CallFrame>> call_frames(
        block.value().transactions.size());
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
    for (size_t i = 0; i < block.value().transactions.size(); ++i) {
        call_tracers.emplace_back(std::make_unique<CallTracer>(
            block.value().transactions[i], call_frames[i]));
    }

    EXPECT_THROW({
        (void)execute_block<EVMC_SHANGHAI>(
            EthereumMainnet{},
            block.value(),
            senders,
            recovered_authorities,
            bs,
            block_hash_buffer,
            pool,
            metrics,
            call_tracers);
    }, MonadException);
}

// test referenced from :
// https://github.com/ethereum/tests/blob/v10.0/BlockchainTests/GeneralStateTests/stRefundTest/refund50_1.json
TYPED_TEST(DBTest, call_frames_refund)
{
    TrieDb tdb{this->db};

    auto const from = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    auto const to = 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba_address;
    auto const ca = 0x095e7baea6a6c7c4c2dfeb977efac326af552d87_address;

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x989680,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {to,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x0,
                          .code_hash = NULL_HASH,
                          .nonce = 0x01}}}},
            {ca,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x1b58,
                          .code_hash = REFUND_TEST_CODE_HASH}},
                 .storage =
                     {{bytes32_t{0x01}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x02}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x03}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x04}, {bytes32_t{}, bytes32_t{0x01}}},
                      {bytes32_t{0x05}, {bytes32_t{}, bytes32_t{0x01}}}}}}},
        Code{{REFUND_TEST_CODE_HASH, REFUND_TEST_ICODE}},
        BlockHeader{.number = 0});

    // clang-format off
    byte_string const block_rlp = evmc::from_hex("0xf9025ff901f7a01e736f5755fc7023588f262b496b6cbc18aa9062d9c7a21b1c709f55ad66aad3a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347942adc25665018aa1fe0e6bc666dac8fc2697ff9baa096841c0823ec823fdb0b0b8ea019c8dd6691b9f335e0433d8cfe59146e8b884ca0f0f9b1e10ec75d9799e3a49da5baeeab089b431b0073fb05fa90035e830728b8a06c8ab36ec0629c97734e8ac823cdd8397de67efb76c7beb983be73dcd3c78141b90100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008302000001830f42408259e78203e800a00000000000000000000000000000000000000000000000000000000000000000880000000000000000f862f860800a830186a094095e7baea6a6c7c4c2dfeb977efac326af552d8780801ba0eac92a424c1599d71b1c116ad53800caa599233ea91907e639b7cb98fa0da3bba06be40f001771af85bfba5e6c4d579e038e6465af3f55e71b9490ab48fcfa5b1ec0")
            .value();
    // clang-format on
    byte_string_view block_rlp_view{block_rlp};
    auto block = rlp::decode_block(block_rlp_view);
    ASSERT_TRUE(!block.has_error());
    EXPECT_EQ(block.value().header.number, 1);

    BlockHashBufferFinalized block_hash_buffer;
    block_hash_buffer.set(
        block.value().header.number - 1, block.value().header.parent_hash);

    BlockState bs(tdb, this->vm);
    BlockMetrics metrics;

    fiber::PriorityPool pool{1, 1};

    auto const recovered_senders =
        recover_senders(block.value().transactions, pool);
    std::vector<Address> senders(block.value().transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        MONAD_ASSERT(recovered_senders[i].has_value());
        senders[i] = recovered_senders[i].value();
    }
    auto const recovered_authorities =
        recover_authorities(block.value().transactions, pool);
    std::vector<std::vector<CallFrame>> call_frames(
        block.value().transactions.size());
    std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
    for (size_t i = 0; i < block.value().transactions.size(); ++i) {
        call_tracers.emplace_back(std::make_unique<CallTracer>(
            block.value().transactions[i], call_frames[i]));
    }

    auto const receipts = execute_block<EVMC_SHANGHAI>(
        ShanghaiEthereumMainnet{},
        block.value(),
        senders,
        recovered_authorities,
        bs,
        block_hash_buffer,
        pool,
        metrics,
        call_tracers);

    ASSERT_TRUE(!receipts.has_error());

    bs.log_debug();

    auto const &transactions = block.value().transactions;
    BlockHeader const header = block.value().header;
    bytes32_t const block_id{header.number};
    bs.commit(
        block_id,
        header,
        receipts.value(),
        call_frames,
        recover_senders(transactions),
        transactions,
        {},
        std::nullopt);
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);

    auto const actual_call_frames =
        read_call_frame(this->db, tdb.get_block_number(), 0);

    ASSERT_EQ(actual_call_frames.size(), 1);
    CallFrame expected{
        .type = CallType::CALL,
        .flags = 0,
        .from = from,
        .to = ca,
        .value = 0,
        .gas = 0x186a0,
        .gas_used = 0x8fd8,
        .status = EVMC_SUCCESS,
        .depth = 0};

    EXPECT_EQ(actual_call_frames[0], expected);
}
