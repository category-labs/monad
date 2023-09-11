#include <gtest/gtest.h>

#include <ethash/keccak.hpp>

#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>

#include <nlohmann/json.hpp>

#include <monad/test/dump_state_from_db.hpp>
#include <monad/test/make_db.hpp>

#include <monad/core/transaction.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state2/state_deltas.hpp>

using namespace monad;

template <typename>
struct StateSerialization : public testing::Test
{
};

using DBTypes =
    ::testing::Types<db::RocksDB, db::InMemoryTrieDB, db::RocksTrieDB>;

TYPED_TEST_SUITE(StateSerialization, DBTypes);

TYPED_TEST(StateSerialization, serialize_add)
{
    /* The following command was used as a post state to test against.
    ./cmake-build-debug/test/ethereum_test/monad-ethereum-test \
     --gtest_catch_exceptions=0 \
     --gtest_filter="VMTests/vmArithmeticTest.add" \
     --dump_state \
     --fork Berlin --txn 0  \
     log_levels \
     --state debug \
     --change_set debug \
     --trie_db debug \
     --evmone debug \
     --ethereum_test debug
     */
    auto db = test::make_db<TypeParam>();
    auto const expected_payload = nlohmann::json::parse(R"(
{
  "0x03601462093b5945d1676df093446790fd31b20e7b12a2e8e5e09d068109616b": {
    "balance": "0xba1a9ce0b9aa781",
    "code": "0x",
    "nonce": "0x1"
  },
  "0x227a737497210f7cc2f464e3bfffadefa9806193ccdf873203cd91c8d3eab518": {
    "balance": "0xba1a9ce0ba1a9ce",
    "code": "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "nonce": "0x0",
    "storage": {
      "0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563": "0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
      "original_account_address": "0x0000000000000000000000000000000000000100"
    }
  },
  "0x4599828688a5c37132b6fc04e35760b4753ce68708a7b7d4d97b940047557fdb": {
    "balance": "0xba1a9ce0ba1a9ce",
    "code": "0x60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "nonce": "0x0"
  },
  "0x4c933a84259efbd4fb5d1522b5255e6118da186a2c71ec5efaa5c203067690b7": {
    "balance": "0xba1a9ce0ba1a9ce",
    "code": "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60010160005500",
    "nonce": "0x0"
  },
  "0x9d860e7bb7e6b09b87ab7406933ef2980c19d7d0192d8939cf6dc6908a03305f": {
    "balance": "0x7024c",
    "code": "0x",
    "nonce": "0x0"
  },
  "0xa17eacbc25cda025e81db9c5c62868822c73ce097cee2a63e33a2e41268358a1": {
    "balance": "0xba1a9ce0ba1a9ce",
    "code": "0x60017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
    "nonce": "0x0"
  },
  "0xa5cc446814c4e9060f2ecb3be03085683a83230981ca8f19d35a4438f8c2d277": {
    "balance": "0xba1a9ce0ba1a9ce",
    "code": "0x600060000160005500",
    "nonce": "0x0"
  },
  "0xf057b39b049c7df5dfa86c4b0869abe798cef059571a5a1e5bbf5168cf6c097b": {
    "balance": "0xba1a9ce0ba1a9cf",
    "code": "0x600060006000600060006004356101000162fffffff100",
    "nonce": "0x0"
  }
})");
    auto const a = 0x0000000000000000000000000000000000000100_address;
    auto const a_code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                       "ffffffffffffffffffffff0160005500")
            .value();
    auto const a_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(a_code.data(), a_code.size()));
    auto const b = 0x0000000000000000000000000000000000000101_address;
    auto const b_code =
        evmc::from_hex("60047ffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffffffff0160005500")
            .value();
    auto const b_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(b_code.data(), b_code.size()));
    auto const c = 0x0000000000000000000000000000000000000102_address;
    auto const c_code =
        evmc::from_hex("60017ffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffffffff0160005500")
            .value();
    auto const c_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(c_code.data(), c_code.size()));
    auto const d = 0x0000000000000000000000000000000000000103_address;
    auto const d_code = evmc::from_hex("600060000160005500").value();
    auto const d_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(d_code.data(), d_code.size()));
    auto const e = 0x0000000000000000000000000000000000000104_address;
    auto const e_code =
        evmc::from_hex("7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                       "fffffffffff60010160005500")
            .value();
    auto const e_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(e_code.data(), e_code.size()));
    auto const f = 0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba_address;
    auto const g = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    auto const h = 0xcccccccccccccccccccccccccccccccccccccccc_address;
    auto const h_code =
        evmc::from_hex("600060006000600060006004356101000162fffffff100")
            .value();
    auto const h_code_hash = std::bit_cast<bytes32_t>(
        ethash::keccak256(h_code.data(), h_code.size()));

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
            {a_code_hash, a_code},
            {b_code_hash, b_code},
            {c_code_hash, c_code},
            {d_code_hash, d_code},
            {e_code_hash, e_code},
            {h_code_hash, h_code}});

    auto const actual_payload = monad::test::dump_state_from_db(db);
    // performs a deep comparison:
    // https://github.com/nlohmann/json/blob/6cc0eaf88f14493719c440dc5c343ee70aa5551f/include/nlohmann/json.hpp#L3687-L3698
    EXPECT_EQ(expected_payload, actual_payload);
}
