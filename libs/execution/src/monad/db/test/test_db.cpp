#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
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
    auto const code1 =
        std::make_shared<CodeAnalysis>(analyze(byte_string{0xab, 0xcd, 0xef}));
    auto const code2 =
        std::make_shared<CodeAnalysis>(analyze(byte_string{0xbb, 0xbb, 0xbb}));
    constexpr auto code_hash1 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto code_hash2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1bbbbbbbbb_bytes32;

    auto const a_code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                       "ffffffffffffffffffffff0160005500")
            .value();
    auto const a_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(a_code.data(), a_code.size()));
    auto const a_code_analysis =
        std::make_shared<CodeAnalysis>(analyze(a_code));
    auto const b_code =
        evmc::from_hex("60047ffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffffffff0160005500")
            .value();
    auto const b_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(b_code.data(), b_code.size()));
    auto const b_code_analysis =
        std::make_shared<CodeAnalysis>(analyze(b_code));
    auto const c_code =
        evmc::from_hex("60017ffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffffffff0160005500")
            .value();
    auto const c_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(c_code.data(), c_code.size()));
    auto const c_code_analysis =
        std::make_shared<CodeAnalysis>(analyze(c_code));
    auto const d_code = evmc::from_hex("600060000160005500").value();
    auto const d_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(d_code.data(), d_code.size()));
    auto const d_code_analysis =
        std::make_shared<CodeAnalysis>(analyze(d_code));
    auto const e_code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff60010160005500")
            .value();
    auto const e_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(e_code.data(), e_code.size()));
    auto const e_code_analysis =
        std::make_shared<CodeAnalysis>(analyze(e_code));
    auto const h_code =
        evmc::from_hex("600060006000600060006004356101000162fffffff100")
            .value();
    auto const h_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(h_code.data(), h_code.size()));
    auto const h_code_analysis =
        std::make_shared<CodeAnalysis>(analyze(h_code));

    auto const json_str = R"(
{
  "0x03601462093b5945d1676df093446790fd31b20e7b12a2e8e5e09d068109616b": {
    "balance": "838137708090664833",
    "code": "0x",
    "nonce": "0x1",
    "storage": {}
  },
  "0x227a737497210f7cc2f464e3bfffadefa9806193ccdf873203cd91c8d3eab518": {
    "balance": "838137708091124174",
    "code":
    "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "nonce": "0x0",
    "storage": {
      "0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563":
      "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"
    }
  },
  "0x4599828688a5c37132b6fc04e35760b4753ce68708a7b7d4d97b940047557fdb": {
    "balance": "838137708091124174",
    "code":
    "0x60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "nonce": "0x0",
    "storage": {}
  },
  "0x4c933a84259efbd4fb5d1522b5255e6118da186a2c71ec5efaa5c203067690b7": {
    "balance": "838137708091124174",
    "code":
    "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60010160005500",
    "nonce": "0x0",
    "storage": {}
  },
  "0x9d860e7bb7e6b09b87ab7406933ef2980c19d7d0192d8939cf6dc6908a03305f": {
    "balance": "459340",
    "code": "0x",
    "nonce": "0x0",
    "storage": {}
  },
  "0xa17eacbc25cda025e81db9c5c62868822c73ce097cee2a63e33a2e41268358a1": {
    "balance": "838137708091124174",
    "code":
    "0x60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "nonce": "0x0",
    "storage": {}
  },
  "0xa5cc446814c4e9060f2ecb3be03085683a83230981ca8f19d35a4438f8c2d277": {
    "balance": "838137708091124174",
    "code": "0x600060000160005500",
    "nonce": "0x0",
    "storage": {}
  },
  "0xf057b39b049c7df5dfa86c4b0869abe798cef059571a5a1e5bbf5168cf6c097b": {
    "balance": "838137708091124175",
    "code": "0x600060006000600060006004356101000162fffffff100",
    "nonce": "0x0",
    "storage": {}
  }
})";

    auto const expected_payload = nlohmann::json::parse(json_str);

    struct InMemoryTrieDbFixture : public ::testing::Test
    {
        static TrieDb make_db(auto &&...args)
        {
            return TrieDb{std::nullopt, std::forward<decltype(args)>(args)...};
        }
    };

    struct OnDiskTrieDbFixture : public ::testing::Test
    {
        static TrieDb make_db(auto &&...args)
        {
            return TrieDb{
                mpt::OnDiskDbConfig{}, std::forward<decltype(args)>(args)...};
        }
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
        TrieDb rw(mpt::OnDiskDbConfig{.dbname_paths = {name}});

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

        TrieDb ro{mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = {name}}};
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 2});
        ro.set_block_number(0);
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 1});

        Account const acct3{.nonce = 3};
        rw.increment_block_number();
        rw.commit(
            StateDeltas{
                {a, StateDelta{.account = {acct2, acct3}, .storage = {}}}},
            Code{});

        EXPECT_FALSE(ro.is_latest());
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 1});

        ro.set_block_number(2);
        EXPECT_EQ(ro.read_account(a), std::nullopt);

        ro.load_latest();
        EXPECT_TRUE(ro.is_latest());
        EXPECT_EQ(ro.read_account(a), Account{.nonce = 3});
    }
    std::filesystem::remove(name);
}

TYPED_TEST(DBTest, read_storage)
{
    Account acct{.nonce = 1};
    auto db = this->make_db();
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage = {{key1, {bytes32_t{}, value1}}}}}},
        Code{});

    // Existing storage
    EXPECT_EQ(db.read_storage(a, key1), value1);

    // Non-existing key
    EXPECT_EQ(db.read_storage(a, key2), bytes32_t{});

    // Non-existing account
    EXPECT_FALSE(db.read_account(b).has_value());
    EXPECT_EQ(db.read_storage(b, key1), bytes32_t{});
}

TYPED_TEST(DBTest, read_code)
{
    Account acct_a{.balance = 1, .code_hash = code_hash1, .nonce = 1};
    auto db = this->make_db();
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, acct_a}}}},
        Code{{code_hash1, code1}});

    EXPECT_EQ(
        db.read_code(code_hash1)->executable_code, code1->executable_code);

    Account acct_b{.balance = 0, .code_hash = code_hash2, .nonce = 1};
    db.commit(
        StateDeltas{{b, StateDelta{.account = {std::nullopt, acct_b}}}},
        Code{{code_hash2, code2}});

    EXPECT_EQ(
        db.read_code(code_hash2)->executable_code, code2->executable_code);
}

TYPED_TEST(DBTest, ModifyStorageOfAccount)
{
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    auto db = this->make_db();
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    acct = db.read_account(a).value();
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{key2, {value2, value1}}}}}},
        Code{});

    EXPECT_EQ(
        db.state_root(),
        0x0169f0b22c30d7d6f0bb7ea2a07be178e216b72f372a6a7bafe55602e5650e60_bytes32);
}

TYPED_TEST(DBTest, touch_without_modify_regression)
{
    auto db = this->make_db();
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, std::nullopt}}}},
        Code{});

    EXPECT_EQ(db.read_account(a), std::nullopt);
    EXPECT_EQ(db.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, delete_account_modify_storage_regression)
{
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};
    auto db = this->make_db();
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, std::nullopt},
                 .storage =
                     {{key1, {value1, value2}}, {key2, {value2, value1}}}}}},
        Code{});

    EXPECT_EQ(db.read_account(a), std::nullopt);
    EXPECT_EQ(db.read_storage(a, key1), bytes32_t{});
    EXPECT_EQ(db.state_root(), NULL_ROOT);
}

TYPED_TEST(DBTest, storage_deletion)
{
    Account acct{.balance = 1'000'000, .code_hash = code_hash1, .nonce = 1337};

    auto db = this->make_db();
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {std::nullopt, acct},
                 .storage =
                     {{key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}},
        Code{});

    acct = db.read_account(a).value();
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account = {acct, acct},
                 .storage = {{key1, {value1, bytes32_t{}}}}}}},
        Code{});

    EXPECT_EQ(
        db.state_root(),
        0xcc04b7a59a7c5d1f294402a0cbe42b5102db928fb2fad9d0d6f8c2a21a34c195_bytes32);
}

TYPED_TEST(DBTest, commit_receipts)
{
    auto db = this->make_db();

    // empty receipts
    db.commit(StateDeltas{}, Code{}, {});
    EXPECT_EQ(db.receipts_root(), NULL_ROOT);

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

    db.commit(StateDeltas{}, Code{}, receipts);
    EXPECT_EQ(
        db.receipts_root(),
        0x7ea023138ee7d80db04eeec9cf436dc35806b00cc5fe8e5f611fb7cf1b35b177_bytes32);

    // A new receipt trie with eip1559 transaction type
    receipts.clear();
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 34865, .type = TransactionType::eip1559});
    receipts.emplace_back(Receipt{
        .status = 1, .gas_used = 77969, .type = TransactionType::eip1559});
    db.commit(StateDeltas{}, Code{}, receipts);
    EXPECT_EQ(
        db.receipts_root(),
        0x61f9b4707b28771a63c1ac6e220b2aa4e441dd74985be385eaf3cd7021c551e9_bytes32);
}

TYPED_TEST(DBTest, to_json)
{
    auto const a = 0x0000000000000000000000000000000000000100_address;
    auto const b = 0x0000000000000000000000000000000000000101_address;
    auto const c = 0x0000000000000000000000000000000000000102_address;
    auto const d = 0x0000000000000000000000000000000000000103_address;
    auto const e = 0x0000000000000000000000000000000000000104_address;
    auto const f = 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba_address;
    auto const g = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    auto const h = 0xcccccccccccccccccccccccccccccccccccccccc_address;

    auto db = this->make_db();
    db.commit(
        StateDeltas{
            {a,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = a_code_hash}},
                 .storage =
                     {{bytes32_t{},
                       {bytes32_t{},
                        0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe_bytes32}}}}},
            {b,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = b_code_hash}}}},
            {c,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = c_code_hash}}}},
            {d,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = d_code_hash}}}},
            {e,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9ce,
                          .code_hash = e_code_hash}}}},
            {f,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 0x7024c}}}},
            {g,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0xba1a9ce0b9aa781, .nonce = 1}}}},
            {h,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0xba1a9ce0ba1a9cf,
                          .code_hash = h_code_hash}}}}},
        Code{
            {a_code_hash, a_code_analysis},
            {b_code_hash, b_code_analysis},
            {c_code_hash, c_code_analysis},
            {d_code_hash, d_code_analysis},
            {e_code_hash, e_code_analysis},
            {h_code_hash, h_code_analysis}});

    EXPECT_EQ(expected_payload, db.to_json());
}

TYPED_TEST(DBTest, construct_from_binary)
{
    std::ifstream accounts(test_resource::checkpoint_dir / "accounts");
    std::ifstream code(test_resource::checkpoint_dir / "code");
    auto db = this->make_db(accounts, code);
    EXPECT_EQ(
        db.state_root(),
        0xb9eda41f4a719d9f2ae332e3954de18bceeeba2248a44110878949384b184888_bytes32);
    EXPECT_EQ(
        db.read_code(a_code_hash)->executable_code,
        a_code_analysis->executable_code);
    EXPECT_EQ(
        db.read_code(b_code_hash)->executable_code,
        b_code_analysis->executable_code);
    EXPECT_EQ(
        db.read_code(c_code_hash)->executable_code,
        c_code_analysis->executable_code);
    EXPECT_EQ(
        db.read_code(d_code_hash)->executable_code,
        d_code_analysis->executable_code);
    EXPECT_EQ(
        db.read_code(e_code_hash)->executable_code,
        e_code_analysis->executable_code);
    EXPECT_EQ(
        db.read_code(h_code_hash)->executable_code,
        h_code_analysis->executable_code);
}
