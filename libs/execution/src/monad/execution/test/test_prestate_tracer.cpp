#include <monad/core/account.hpp>
#include <monad/execution/trace/prestate_tracer.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/account_state.hpp>
#include <monad/state3/state.hpp>

#include <gtest/gtest.h>
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
    State s(bs, Incarnation{0, 0});

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

    EXPECT_EQ(state_to_json(prestate, s), nlohmann::json::parse(json_str));
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
    State s(bs, Incarnation{0, 0});

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
        state_deltas_to_json(state_deltas, s), nlohmann::json::parse(json_str));
}
