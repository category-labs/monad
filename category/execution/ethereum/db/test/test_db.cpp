#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex_literal.hpp>
#include <category/core/keccak.hpp>
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
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
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
#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

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

    // clang-format off
    auto const CA1_CODE = 
        evmc::from_hex("0x3373fffffffffffffffffffffffffffffffffffffffe14604d57602036146024575f5ffd5b5f35801560495762001fff810690815414603c575f5ffd5b62001fff01545f5260205ff35b5f5ffd5b62001fff42064281555f359062001fff015500")
            .value();
    // clang-format on
    auto const CA1_CODE_HASH = to_bytes(keccak256(CA1_CODE));
    auto const CA1_CODE_ICODE = vm::make_shared_intercode(CA1_CODE);

    // clang-format off
    auto const CA2_CODE = 
        evmc::from_hex("0x3060025560206000600039602060006000f000")
            .value();
    // clang-format on
    auto const CA2_CODE_HASH = to_bytes(keccak256(CA2_CODE));
    auto const CA2_CODE_ICODE = vm::make_shared_intercode(CA2_CODE);

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

    struct CancunEthereumMainnet : EthereumMainnet
    {
        virtual evmc_revision get_revision(
            uint64_t /* block_number */,
            uint64_t /* timestamp */) const override
        {
            return EVMC_CANCUN;
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

    byte_string read_trace(
        unsigned char nibble, mpt::Db &db, uint64_t const block_number,
        uint64_t const tx_idx)
    {
        using namespace mpt;

        using KeyedChunk = std::pair<Nibbles, byte_string>;

        Nibbles const min = mpt::concat(
            FINALIZED_NIBBLE,
            nibble,
            NibblesView{serialize_as_big_endian<sizeof(uint32_t)>(tx_idx)});
        Nibbles const max = mpt::concat(
            FINALIZED_NIBBLE,
            nibble,
            NibblesView{serialize_as_big_endian<sizeof(uint32_t)>(tx_idx + 1)});

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

        return std::accumulate(
            std::make_move_iterator(chunks.begin()),
            std::make_move_iterator(chunks.end()),
            byte_string{},
            [](byte_string const acc, KeyedChunk const chunk) {
                return std::move(acc) + std::move(chunk.second);
            });
    }

    std::vector<CallFrame> read_call_frame(
        mpt::Db &db, uint64_t const block_number, uint64_t const tx_idx)
    {
        byte_string const call_frame_bs =
            read_trace(CALL_FRAME_NIBBLE, db, block_number, tx_idx);
        byte_string_view view{call_frame_bs};
        auto const call_frame = rlp::decode_call_frames(view);
        MONAD_ASSERT(!call_frame.has_error());
        MONAD_ASSERT(view.empty());
        return call_frame.value();
    }

    nlohmann::json read_pre_state_traces(
        mpt::Db &db, uint64_t const block_number, uint64_t const tx_idx)
    {
        auto const trace_bs =
            read_trace(PRE_STATE_TRACE_NIBBLE, db, block_number, tx_idx);
        std::vector<uint8_t> trace_cbor(trace_bs.begin(), trace_bs.end());
        return nlohmann::json::from_msgpack(trace_cbor);
    }

    nlohmann::json read_state_deltas_traces(
        mpt::Db &db, uint64_t const block_number, uint64_t const tx_idx)
    {
        auto const trace_bs =
            read_trace(STATE_DELTAS_TRACE_NIBBLE, db, block_number, tx_idx);
        std::vector<uint8_t> trace_cbor(trace_bs.begin(), trace_bs.end());
        return nlohmann::json::from_msgpack(trace_cbor);
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
    EXPECT_EQ(byte_string_view(a_icode->code(), a_icode->code_size()), A_CODE);

    Account acct_b{.balance = 0, .code_hash = B_CODE_HASH, .nonce = 1};
    commit_sequential(
        tdb,
        StateDeltas{{ADDR_B, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{B_CODE_HASH, B_ICODE}},
        BlockHeader{.number = 1});

    auto const b_icode = tdb.read_code(B_CODE_HASH);
    EXPECT_EQ(byte_string_view(b_icode->code(), b_icode->code_size()), B_CODE);
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
    std::vector<PreState> pre_state_traces;
    pre_state_traces.resize(receipts.size());
    std::vector<StateDeltas> state_deltas_traces;
    state_deltas_traces.resize(receipts.size());
    constexpr uint64_t first_block = 1;
    std::vector<Address> senders = recover_senders(transactions);
    commit_sequential(
        tdb,
        StateDeltas{},
        Code{},
        BlockHeader{.number = first_block},
        receipts,
        call_frames,
        pre_state_traces,
        state_deltas_traces,
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
    pre_state_traces.resize(receipts.size());
    state_deltas_traces.resize(receipts.size());
    senders = recover_senders(transactions);
    commit_sequential(
        tdb,
        StateDeltas{},
        Code{},
        BlockHeader{.number = second_block},
        receipts,
        call_frames,
        pre_state_traces,
        state_deltas_traces,
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
        byte_string_view(a_icode->code(), a_icode->code_size()),
        byte_string_view(A_ICODE->code(), A_ICODE->code_size()));
    auto const b_icode = tdb.read_code(B_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(b_icode->code(), b_icode->code_size()),
        byte_string_view(B_ICODE->code(), B_ICODE->code_size()));
    auto const c_icode = tdb.read_code(C_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(c_icode->code(), c_icode->code_size()),
        byte_string_view(C_ICODE->code(), C_ICODE->code_size()));
    auto const d_icode = tdb.read_code(D_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(d_icode->code(), d_icode->code_size()),
        byte_string_view(D_ICODE->code(), D_ICODE->code_size()));
    auto const e_icode = tdb.read_code(E_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(e_icode->code(), e_icode->code_size()),
        byte_string_view(E_ICODE->code(), E_ICODE->code_size()));
    auto const h_icode = tdb.read_code(H_CODE_HASH);
    EXPECT_EQ(
        byte_string_view(h_icode->code(), h_icode->code_size()),
        byte_string_view(H_ICODE->code(), H_ICODE->code_size()));
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
    std::vector<PreState> pre_state_traces(NUM_TXNS);
    std::vector<StateDeltas> state_deltas_traces(NUM_TXNS);
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
        pre_state_traces,
        state_deltas_traces,
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

TYPED_TEST(DBTest, commit_prestate_traces)
{
    TrieDb tdb{this->db};
    vm::VM vm{};

    BlockState bs(tdb, vm);
    
    PreState pre_state;
    {
        Account a{.balance = 0x20000, .nonce = 1};
        AccountState as{a};
        pre_state.emplace(ADDR_A, as);
    }
    {
        Account b{.balance = 0x100100, .code_hash = B_CODE_HASH, .nonce = 1337};
        AccountState bs{b};
        bs.storage_.emplace(key1, value1);
        bs.storage_.emplace(key2, value2);
        pre_state.emplace(ADDR_B, bs);
    }
    nlohmann::json const expected_json = state_to_json(pre_state);

    constexpr uint64_t NUM_TXNS = 1000;

    static byte_string const encoded_txn = byte_string{0x1a, 0x1b, 0x1c};
    std::vector<PreState> pre_state_traces{};
    std::vector<StateDeltas> state_deltas_traces(NUM_TXNS);
    std::vector<std::vector<CallFrame>> call_frames(NUM_TXNS);
    for (uint64_t txn = 0; txn < NUM_TXNS; ++txn) {
        pre_state_traces.emplace_back(pre_state);
    }
    std::vector<Receipt> const receipts(NUM_TXNS);
    // need to increment the nonce of transactions
    std::vector<Transaction> transactions;
    for (uint64_t nonce = 0; nonce < NUM_TXNS; ++nonce) {
        transactions.push_back(Transaction{.nonce = nonce});
    }
    std::vector<Address> const senders(NUM_TXNS);
    commit_sequential(
        tdb,
        StateDeltas{},
        Code{},
        BlockHeader{},
        receipts,
        call_frames,
        pre_state_traces,
        state_deltas_traces,
        senders,
        transactions);

    for (uint64_t txn = 0; txn < NUM_TXNS; ++txn) {
        auto const &res_json =
            read_pre_state_traces(this->db, tdb.get_block_number(), txn);
        ASSERT_TRUE(!res_json.empty());
        EXPECT_EQ(res_json, expected_json);
    }
}

TYPED_TEST(DBTest, commit_state_deltas_traces)
{
    TrieDb tdb{this->db};
    vm::VM vm{};

    BlockState bs(tdb, vm);
    
    auto const state_deltas = StateDeltas{
        {ADDR_A,
         StateDelta{
             .account =
                 {Account{.balance = 0x200000, .nonce = 0},
                  Account{.balance = 0x1f0000, .nonce = 1}}}},
        {ADDR_B,
         StateDelta{
             .account =
                 {Account{.balance = 0, .nonce = 0},
                  Account{.balance = 0x10000}},
             .storage =
                 {{key1, {bytes32_t{}, value1}}, {key2, {value1, value2}}}}},
    };

    nlohmann::json const expected_json = state_deltas_to_json(state_deltas);

    constexpr uint64_t NUM_TXNS = 1000;

    static byte_string const encoded_txn = byte_string{0x1a, 0x1b, 0x1c};
    std::vector<PreState> pre_state_traces(NUM_TXNS);
    std::vector<StateDeltas> state_deltas_traces{};
    std::vector<std::vector<CallFrame>> call_frames(NUM_TXNS);
    for (uint64_t txn = 0; txn < NUM_TXNS; ++txn) {
        state_deltas_traces.emplace_back(state_deltas);
    }
    std::vector<Receipt> const receipts(NUM_TXNS);
    // need to increment the nonce of transactions
    std::vector<Transaction> transactions;
    for (uint64_t nonce = 0; nonce < NUM_TXNS; ++nonce) {
        transactions.push_back(Transaction{.nonce = nonce});
    }
    std::vector<Address> const senders(NUM_TXNS);
    commit_sequential(
        tdb,
        StateDeltas{},
        Code{},
        BlockHeader{},
        receipts,
        call_frames,
        pre_state_traces,
        state_deltas_traces,
        senders,
        transactions);

    for (uint64_t txn = 0; txn < NUM_TXNS; ++txn) {
        auto const &res_json =
            read_state_deltas_traces(this->db, tdb.get_block_number(), txn);
        ASSERT_TRUE(!res_json.empty());
        EXPECT_EQ(res_json, expected_json);
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
    auto const results = execute_block<EVMC_SHANGHAI>(
        EthereumMainnet{},
        block.value(),
        senders,
        bs,
        block_hash_buffer,
        pool,
        metrics);

    ASSERT_TRUE(!results.has_error());

    bs.log_debug();

    std::vector<Receipt> receipts;
    std::vector<std::vector<CallFrame>> call_frames;
    for (auto &result : results.value()) {
        receipts.emplace_back(std::move(result.receipt));
        call_frames.emplace_back(std::move(result.call_frames));
    }
    std::vector<PreState> const pre_state_traces(receipts.size());
    std::vector<StateDeltas> const state_deltas_traces(receipts.size());
    auto const &transactions = block.value().transactions;
    BlockHeader const header{.number = 1};
    bytes32_t const block_id{header.number};
    bs.commit(
        block_id,
        header,
        receipts,
        call_frames,
        pre_state_traces,
        state_deltas_traces,
        recover_senders(transactions),
        transactions,
        {},
        {});
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);

    auto const actual_call_frames =
        read_call_frame(this->db, tdb.get_block_number(), 0);

#ifdef ENABLE_CALL_TRACING
    EXPECT_EQ(actual_call_frames.size(), 35799);
#else
    EXPECT_EQ(actual_call_frames.size(), 0);
#endif
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
    auto const results = execute_block<EVMC_SHANGHAI>(
        ShanghaiEthereumMainnet{},
        block.value(),
        senders,
        bs,
        block_hash_buffer,
        pool,
        metrics);

    ASSERT_TRUE(!results.has_error());

    bs.log_debug();

    std::vector<Receipt> receipts;
    std::vector<std::vector<CallFrame>> call_frames;
    for (auto &result : results.value()) {
        receipts.emplace_back(std::move(result.receipt));
        call_frames.emplace_back(std::move(result.call_frames));
    }
    std::vector<PreState> const pre_state_traces(receipts.size());
    std::vector<StateDeltas> const state_deltas_traces(receipts.size());

    auto const &transactions = block.value().transactions;
    BlockHeader const header = block.value().header;
    bytes32_t const block_id{header.number};
    bs.commit(
        block_id,
        header,
        receipts,
        call_frames,
        pre_state_traces,
        state_deltas_traces,
        recover_senders(transactions),
        transactions,
        {},
        std::nullopt);
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);

    auto const actual_call_frames =
        read_call_frame(this->db, tdb.get_block_number(), 0);

#ifdef ENABLE_CALL_TRACING
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
#else
    EXPECT_EQ(actual_call_frames.size(), 0);
#endif
}

// test reference from:
// https://github.com/ethereum/tests/blob/e46e1db503ee2711ad02e1f5b3ea45d43e9cd8cb/BlockchainTests/GeneralStateTests/stInitCodeTest/CallRecursiveContract.json
TYPED_TEST(DBTest, prestate_trace_test)
{
    TrieDb tdb{this->db};
    vm::VM vm{};

    auto const from = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    auto const ca1 = 0x000f3df6d732807ef1319fb7b8bb8522d0beac02_address;
    auto const ca2 = 0x095e7baea6a6c7c4c2dfeb977efac326af552d87_address;

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
            {ca1,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x0,
                          .code_hash = CA1_CODE_HASH,
                          .nonce = 0x01}}}},
            {ca2,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0x28, .code_hash = CA2_CODE_HASH}}}}},
        Code{
            {CA1_CODE_HASH, CA1_CODE_ICODE},
            {CA2_CODE_HASH, CA2_CODE_ICODE},
        },
        BlockHeader{.number = 0});

    // clang-format off
    byte_string const block_rlp = evmc::from_hex("0xf902a4f9023ba072dba3cc0c0508842208e4db53246154a9b7143b63bd3af54183e9664577ca43a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347942adc25665018aa1fe0e6bc666dac8fc2697ff9baa007db5f315754432195b1954616123a44627d91bacb6c4c12a33ed9de27182901a05b7703b5c43ffb90d35cb2929bc59b874eeecc3e753bbcd8cb6f522ec02a86bda024a18d364b1ee6377484245abffe445a18a35d1d6962c97ea3cd3477dbd3e985b901000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080018405f5e1008305d8a38203e800a000000000000000000000000000000000000000000000000000000000000200008800000000000000000aa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b4218080a00000000000000000000000000000000000000000000000000000000000000000f862f860800a83061a8094095e7baea6a6c7c4c2dfeb977efac326af552d8701001ca0330a37bd0d233b9945f18b10d7ec2035befd8c2cef7f2f3dd21dfd7d0d7da247a07c82e786a416f4f46742e593a1cd6a6c9e7eb86417d211f160f165b55a859bf0c0c0")
            .value();
    // clang-format on
    byte_string_view block_rlp_view{block_rlp};
    auto block = rlp::decode_block(block_rlp_view);
    ASSERT_TRUE(!block.has_error());
    EXPECT_EQ(block.value().header.number, 1);

    BlockHashBufferFinalized block_hash_buffer;
    block_hash_buffer.set(
        block.value().header.number - 1, block.value().header.parent_hash);

    BlockState bs(tdb, vm);
    BlockMetrics metrics;

    fiber::PriorityPool pool{1, 1};

    auto const recovered_senders =
        recover_senders(block.value().transactions, pool);
    std::vector<Address> senders(block.value().transactions.size());
    for (unsigned i = 0; i < recovered_senders.size(); ++i) {
        MONAD_ASSERT(recovered_senders[i].has_value());
        senders[i] = recovered_senders[i].value();
    }

    auto const results = execute_block<EVMC_CANCUN>(
        CancunEthereumMainnet{},
        block.value(),
        senders,
        bs,
        block_hash_buffer,
        pool, metrics);

    ASSERT_TRUE(!results.has_error());

    bs.log_debug();

    std::vector<Receipt> receipts;
    std::vector<std::vector<CallFrame>> call_frames;
    std::vector<PreState> pre_state_traces;
    std::vector<StateDeltas> state_deltas_traces;
    for (auto &result : results.value()) {
        receipts.emplace_back(std::move(result.receipt));
        call_frames.emplace_back(std::move(result.call_frames));
        pre_state_traces.emplace_back(std::move(result.pre_state));
        state_deltas_traces.emplace_back(std::move(result.state_deltas));
    }

    auto const &transactions = block.value().transactions;
    
    auto block_id = bytes32_t{NULL_HASH_BLAKE3};

    bs.commit(
        block_id,
        block.value().header,
        receipts,
        call_frames,
        pre_state_traces,
        state_deltas_traces,
        recover_senders(transactions),
        transactions,
        {},
        std::nullopt);
    tdb.finalize(1, block_id);
    tdb.set_block_and_prefix(1);

    auto const actual_pre_state_traces =
        read_pre_state_traces(this->db, tdb.get_block_number(), 0);
    auto const actual_state_deltas_traces =
        read_state_deltas_traces(this->db, tdb.get_block_number(), 0);

#ifdef ENABLE_PRESTATE_TRACING

    // PreState
    auto const expected_pre_state_traces = R"(
        {
            "0x095e7baea6a6c7c4c2dfeb977efac326af552d87":{
                "balance":"0x28",
                "code_hash":"0x2c80a521f0a06ac0974795a9de86a1c39fb19c2031a168584d45723a2d389d32",
                "storage":{
                    "0x0000000000000000000000000000000000000000000000000000000000000002":"0x0000000000000000000000000000000000000000000000000000000000000000"
                }
            },
            "0x283b585ba5bc85d64a99cb5ecb9a8495ac944948":{
                "balance":"0x0"
            },
            "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba":{
                "balance":"0x0"
            },
            "0x4326e4b5aa29095a293f86c51e4776beeeb13c9b":{
                "balance":"0x0"
            },
            "0x6965235e025001fb620d441803fedb005f7ac710":{
                "balance":"0x0"
            },
            "0x91ed00a0a906270d466af043c4e111dadca970a3":{
                "balance":"0x0"
            },
            "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b":{
                "balance":"0x989680",
                "code_hash":"0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
            },
            "0xb679828fa6040990410b3282e916bfbd6c74f890":{
                "balance":"0x0"
            },
            "0xd2571607e241ecf590ed94b12d87c94babe36db6":{
                "balance":"0x0"
            }
        }
    )";
    EXPECT_EQ(
        actual_pre_state_traces,
        nlohmann::json::parse(expected_pre_state_traces));

    // StateDelta
    auto const expected_state_delta_traces = R"(
        {
        "post": {
            "0x095e7baea6a6c7c4c2dfeb977efac326af552d87": {
            "balance": "0x29",
            "nonce": 1,
            "storage": {
                "0x0000000000000000000000000000000000000000000000000000000000000002": "0x000000000000000000000000095e7baea6a6c7c4c2dfeb977efac326af552d87"
            }
            },
            "0x283b585ba5bc85d64a99cb5ecb9a8495ac944948": {
            "balance": "0x0",
            "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            "nonce": 2
            },
            "0x6965235e025001fb620d441803fedb005f7ac710": {
            "balance": "0x0",
            "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            "nonce": 2
            },
            "0x91ed00a0a906270d466af043c4e111dadca970a3": {
            "balance": "0x0",
            "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            "nonce": 2
            },
            "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b": {
            "balance": "0x5e2021",
            "nonce": 1
            },
            "0xb679828fa6040990410b3282e916bfbd6c74f890": {
            "balance": "0x0",
            "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            "nonce": 2
            },
            "0xd2571607e241ecf590ed94b12d87c94babe36db6": {
            "balance": "0x0",
            "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470",
            "nonce": 2
            }
        },
        "pre": {
            "0x095e7baea6a6c7c4c2dfeb977efac326af552d87": {
            "balance": "0x28",
            "code_hash": "0x2c80a521f0a06ac0974795a9de86a1c39fb19c2031a168584d45723a2d389d32"
            },
            "0x283b585ba5bc85d64a99cb5ecb9a8495ac944948": {
            "balance": "0x0"
            },
            "0x6965235e025001fb620d441803fedb005f7ac710": {
            "balance": "0x0"
            },
            "0x91ed00a0a906270d466af043c4e111dadca970a3": {
            "balance": "0x0"
            },
            "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b": {
            "balance": "0x989680",
            "code_hash": "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
            },
            "0xb679828fa6040990410b3282e916bfbd6c74f890": {
            "balance": "0x0"
            },
            "0xd2571607e241ecf590ed94b12d87c94babe36db6": {
            "balance": "0x0"
            }
        }
        }
    )";
    EXPECT_EQ(
        actual_state_deltas_traces,
        nlohmann::json::parse(expected_state_delta_traces));
#else
    EXPECT_EQ(actual_pre_state_traces.size(), 0);
    EXPECT_EQ(actual_state_deltas_traces.size(), 0)
#endif
}
