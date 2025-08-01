#include <category/core/byte_string.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>

#include <ankerl/unordered_dense.h>
#include <boost/fiber/future/promise.hpp>
#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <nlohmann/json.hpp>

#include <test_resource_data.h>

using namespace monad;
using namespace monad::test;

namespace
{
    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto key3 =
        0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
    constexpr auto value1 =
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
    constexpr auto value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
    constexpr auto value3 =
        0x000000000000000000000000000000000000000000000000000000000000000a_bytes32;
}

TEST(PrestateTracer, pre_state_to_json)
{
    Account const a{.balance = 1000, .code_hash = A_CODE_HASH, .nonce = 1};
    AccountState as{a};
    as.storage_.emplace(key1, value1);
    as.storage_.emplace(key2, value2);
    as.storage_.emplace(key3, value3);

    PreState prestate;
    prestate.emplace(ADDR_A, as);

    // The State setup is only used to get code
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        StateDeltas{},
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State st(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "0x0000000000000000000000000000000000000100":{
            "balance":"0x3e8",
            "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
            "nonce":1,
            "storage":{
                "0x00000000000000000000000000000000000000000000000000000000cafebabe":"0x0000000000000000000000000000000000000000000000000000000000000003",
                "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c":"0x0000000000000000000000000000000000000000000000000000000000000007",
                "0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b":"0x000000000000000000000000000000000000000000000000000000000000000a"
            }
        }
        
    })";

    EXPECT_EQ(state_to_json(prestate, &st), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, state_deltas_to_json)
{
    Account a{.balance = 500, .code_hash = A_CODE_HASH, .nonce = 1};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas{
        {ADDR_A,
         StateDelta{
             .account = {std::nullopt, a},
             .storage = {
                 {key1, {bytes32_t{}, value1}},
                 {key2, {bytes32_t{}, value1}},
             }}}};

    commit_sequential(
        tdb,
        state_deltas,
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State st(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "post":{
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x1f4",
                "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
                "nonce":1,
                "storage":{
                    "0x00000000000000000000000000000000000000000000000000000000cafebabe":"0x0000000000000000000000000000000000000000000000000000000000000003",
                    "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c":"0x0000000000000000000000000000000000000000000000000000000000000003"
                }
            }
        },
        "pre":{"0x0000000000000000000000000000000000000100":{"balance":"0x0"}}
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas, &st), nlohmann::json::parse(json_str));
}

/*
    All the following tests test both the prestate tracer and the statediff
    tracer
*/
// Same setup as CallTrace.execute_success
TEST(PrestateTracer, transfer_success)
{
    using intx::operator""_u256;

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm{};

    commit_sequential(
        tdb,
        StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 0x200000,
                          .code_hash = NULL_HASH,
                          .nonce = 0x0}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 0, .code_hash = NULL_HASH}}}}},
        Code{},
        BlockHeader{});

    EthereumMainnet const chain{};
    BlockHeader const header{
        .number = 1, .gas_limit = 0x100000, .beneficiary = ADDR_A};
    BlockState bs{tdb, vm};
    BlockHashBufferFinalized buffer{};
    BlockMetrics metrics;

    Transaction const tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
        .max_fee_per_gas = 1,
        .gas_limit = 0x100000,
        .value = 0x10000,
        .to = ADDR_B,
    };

    auto const &sender = ADDR_A;

    boost::fibers::promise<void> prev{};
    prev.set_value();

    auto const result =
        execute<EVMC_CANCUN>(chain, 0, tx, sender, header, buffer, bs, metrics, prev);
    ASSERT_TRUE(result.has_value());

    auto const prestate_trace = result.value().pre_state;
    auto const state_deltas_trace = result.value().state_deltas;

    // Prestate
    {
        PreState prestate_expected{};
        {
            Account const from_acct{.balance = 0x200000, .nonce = 0};
            AccountState from_as{from_acct};
            prestate_expected.emplace(ADDR_A, from_as);

            Account const to_acct{
                .balance = 0,
                .nonce = 0,
            };
            AccountState to_as{to_acct};
            prestate_expected.emplace(ADDR_B, to_as);
        }

        EXPECT_EQ(prestate_trace, prestate_expected);
    }

    // StateDiff
    {
        auto const state_deltas_expected = StateDeltas{
            {ADDR_A,
             StateDelta{
                 .account =
                     {Account{.balance = 0x200000, .nonce = 0},
                      Account{.balance = 0x1f0000, .nonce = 1}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {Account{.balance = 0, .nonce = 0},
                      Account{.balance = 0x10000}}}},
        };

        EXPECT_EQ(state_deltas_trace, state_deltas_expected);
    }
}

// TODO: Add more tests
