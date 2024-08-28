#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/state2/state_deltas.hpp>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <ethash/keccak.hpp>

#include <nlohmann/json_fwd.hpp>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <bit>
#include <filesystem>
#include <fstream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::test;

namespace
{
    constexpr auto a = 0x5353535353535353535353535353535353535353_address;
    constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto value1 =
        0x0000000000000013370000000000000000000000000000000000000000000003_bytes32;
    constexpr auto value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
    constexpr auto code_hash1 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;

    struct InMemoryTrieDbFixture : public ::testing::Test
    {
        static constexpr bool on_disk = false;

        InMemoryMachine machine;
        mpt::Db db{machine};
    };

    struct OnDiskTrieDbFixture : public ::testing::Test
    {
        static constexpr bool on_disk = true;

        OnDiskMachine machine;
        mpt::Db db{machine, mpt::OnDiskDbConfig{}};
    };
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
        rw.commit(
            StateDeltas{
                {a,
                 StateDelta{.account = {std::nullopt, acct1}, .storage = {}}}},
            Code{});
        Account const acct2{.nonce = 2};
        rw.increment_block_number();
        rw.commit(
            StateDeltas{
                {a, StateDelta{.account = {acct1, acct2}, .storage = {}}}},
            Code{});

        mpt::Db db2(mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {name}});
        TrieDb ro{db2};
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 2});
        ro.set_block_number(0);
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 1});

        Account const acct3{.nonce = 3};
        rw.increment_block_number();
        rw.commit(
            StateDeltas{
                {a, StateDelta{.account = {acct2, acct3}, .storage = {}}}},
            Code{});

        // Read block 0
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 1});
        // Go forward to block 2
        ro.set_block_number(2);
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 3});
        // Go backward to block 1
        ro.set_block_number(1);
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 2});
        // Setting the same block number is no-op.
        ro.set_block_number(1);
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 2});
        // Go to a random block
        ro.set_block_number(1337);
        EXPECT_EQ(ro.read_account(a), std::nullopt);
    }
    std::filesystem::remove(name);
}

TYPED_TEST(DBTest, read_storage)
{
    Account acct{.nonce = 1};
    TrieDb tdb{this->db};
    tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    // Existing storage
    EXPECT_EQ(tdb.read_storage(a, Incarnation{0, 0}, key1), value1);
    EXPECT_EQ(tdb.read_storage_and_slot(a, key1).first, key1);

    // Non-existing key
    EXPECT_EQ(tdb.read_storage(a, Incarnation{0, 0}, key2), bytes32_t{});
    EXPECT_EQ(tdb.read_storage_and_slot(a, key2).first, bytes32_t{});

    // Non-existing account
    EXPECT_FALSE(tdb.read_account(b).has_value());
    EXPECT_EQ(tdb.read_storage(b, Incarnation{0, 0}, key1), bytes32_t{});
    EXPECT_EQ(tdb.read_storage_and_slot(b, key1).first, bytes32_t{});
}

TYPED_TEST(DBTest, read_code)
{
    auto const code1 =
        std::make_shared<CodeAnalysis>(analyze(byte_string{0xab, 0xcd, 0xef}));
    auto const code2 =
        std::make_shared<CodeAnalysis>(analyze(byte_string{0xbb, 0xbb, 0xbb}));
    constexpr auto code_hash2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1bbbbbbbbb_bytes32;

    Account acct_a{.balance = 1, .code_hash = code_hash1, .nonce = 1};
    TrieDb tdb{this->db};
    tdb.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct_a}}}},
        Code{{code_hash1, code1}});

    EXPECT_EQ(
        tdb.read_code(code_hash1)->executable_code, code1->executable_code);

    Account acct_b{.balance = 0, .code_hash = code_hash2, .nonce = 1};
    tdb.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{code_hash2, code2}});

    EXPECT_EQ(
        tdb.read_code(code_hash2)->executable_code, code2->executable_code);
}

TYPED_TEST(DBTest, ModifyStorageOfAccount)
{
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    TrieDb tdb{this->db};
    tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    acct = tdb.read_account(a).value();
    tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{key2, {value2, value1}}}}}},
        Code{});

    EXPECT_EQ(
        tdb.state_root(),
        0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
}

TYPED_TEST(DBTest, touch_without_modify_regression)
{
    TrieDb tdb{this->db};
    tdb.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, std::nullopt}}}},
        Code{});

    EXPECT_EQ(tdb.read_account(a), std::nullopt);
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, delete_account_modify_storage_regression)
{
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    TrieDb tdb{this->db};
    tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, std::nullopt},
                 .storage =
                     {{key1, {value1, value2}}, {key2, {value2, value1}}}}}},
        Code{});

    EXPECT_EQ(tdb.read_account(a), std::nullopt);
    EXPECT_EQ(tdb.read_storage(a, Incarnation{0, 0}, key1), bytes32_t{});
    EXPECT_EQ(tdb.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, storage_deletion)
{
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    TrieDb tdb{this->db};
    tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    acct = tdb.read_account(a).value();
    tdb.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{key1, {value1, bytes32_t{}}}}}}},
        Code{});

    EXPECT_EQ(
        tdb.state_root(),
        0xcc04b7a59a7c5d1f294402a0cbe42b5102db928fb2fad9d0d6f8c2a21a34c195_bytes32);
}

TYPED_TEST(DBTest, commit_receipts)
{
    TrieDb tdb{this->db};
    // empty receipts
    tdb.commit(StateDeltas{}, Code{}, {});
    EXPECT_EQ(tdb.receipts_root(), NULL_ROOT);

    std::vector<Receipt> receipts;
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 21'000, .type = TransactionType::legacy});
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 42'000, .type = TransactionType::legacy});

    // receipt with log
    Receipt r{.status = 1, .gas_used = 65'092, .type = TransactionType::legacy};
    r.add_log(Receipt::Log{
        .data = from_hex("0x000000000000000000000000000000000000000000000000000"
                         "000000000000000000000000000000000000043b2126e7a22e0c2"
                         "88dfb469e3de4d2c097f3ca000000000000000000000000000000"
                         "0000000000000000001195387bce41fd499000000000000000000"
                         "0000000000000000000000000000000000000000000000"),
        .topics =
            {0xf341246adaac6f497bc2a656f546ab9e182111d630394f0c57c710a59a2cb567_bytes32},
        .address = 0x8d12a197cb00d4747a1fe03395095ce2a5cc6819_address});
    receipts.push_back(std::move(r));

    tdb.commit(StateDeltas{}, Code{}, receipts);
    EXPECT_EQ(
        tdb.receipts_root(),
        0x7ea023138ee7d80db04eeec9cf436dc35806b00cc5fe8e5f611fb7cf1b35b177_bytes32);

    // A new receipt trie with eip1559 transaction type
    receipts.clear();
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 34865, .type = TransactionType::eip1559});
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 77969, .type = TransactionType::eip1559});
    tdb.commit(StateDeltas{}, Code{}, receipts);
    EXPECT_EQ(
        tdb.receipts_root(),
        0x61f9b4707b28771a63c1ac6e220b2aa4e441dd74985be385eaf3cd7021c551e9_bytes32);
}

TYPED_TEST(DBTest, to_json)
{
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

    if (this->on_disk) {
        // also test to_json from a read only db
        mpt::Db db2{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {dbname}}};
        auto ro_db = TrieDb{db2};
        EXPECT_EQ(expected_payload, ro_db.to_json());
    }
    EXPECT_EQ(expected_payload, tdb.to_json());
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
    EXPECT_EQ(
        tdb.read_code(a_code_hash)->executable_code,
        a_code_analysis->executable_code);
    EXPECT_EQ(
        tdb.read_code(b_code_hash)->executable_code,
        b_code_analysis->executable_code);
    EXPECT_EQ(
        tdb.read_code(c_code_hash)->executable_code,
        c_code_analysis->executable_code);
    EXPECT_EQ(
        tdb.read_code(d_code_hash)->executable_code,
        d_code_analysis->executable_code);
    EXPECT_EQ(
        tdb.read_code(e_code_hash)->executable_code,
        e_code_analysis->executable_code);
    EXPECT_EQ(
        tdb.read_code(h_code_hash)->executable_code,
        h_code_analysis->executable_code);
}
