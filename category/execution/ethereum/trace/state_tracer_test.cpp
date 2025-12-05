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

#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <monad/test/traits_test.hpp>

#include <gtest/gtest.h>
#include <intx/intx.hpp>
#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <bit>

using namespace monad;
using namespace monad::test;
using namespace monad::trace;

namespace
{
    constexpr auto key1 =
        0x00000000000000000000000000000000000000000000000000000000cafebabe_bytes32;
    constexpr auto key2 =
        0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c_bytes32;
    constexpr auto key3 =
        0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b_bytes32;
    constexpr auto key4 =
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;
    constexpr auto key5 =
        0x59fb7853eb21f604d010b94c123acbeae621f09ce15ee5d7616485b1e78a72e9_bytes32;
    constexpr auto key6 =
        0x8d8ebb65ec00cb973d4fe086a607728fd1b9de14aa48208381eed9592f0dee9a_bytes32;
    constexpr auto key7 =
        0xff896b09014882056009dedb136458f017fcef9a4729467d0d00b4fd413fb1f1_bytes32;
    constexpr auto value1 =
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32;
    constexpr auto value2 =
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32;
    constexpr auto value3 =
        0x000000000000000000000000000000000000000000000000000000000000000a_bytes32;
    constexpr auto value4 =
        0x000000000000000000000000000000000000000000000000000000000024aea6_bytes32;
    constexpr auto value5 =
        0x00000000000000c42b56a52aedf18667c8ae258a0280a8912641c80c48cd9548_bytes32;
    constexpr auto value6 =
        0x00000000000000784ae4881e40b1f5ebb4437905fbb8a5914454123b0293b35f_bytes32;
    constexpr auto value7 =
        0x000000000000000e78ac39cb1c20e9edc753623b153705d0ccc487e31f9d6749_bytes32;

    constexpr auto addr1 = 0x0000000000000000000000000000000000000002_address;
    constexpr auto addr2 = 0x008b3b2f992c0e14edaa6e2c662bec549caa8df1_address;
    constexpr auto addr3 = 0x35a9f94af726f07b5162df7e828cc9dc8439e7d0_address;
    constexpr auto addr4 = 0xc8ba32cab1757528daf49033e3673fae77dcf05d_address;
    constexpr auto addr5 = 0xe02ad958162c9acb9c3eb90f67b02db21b10d3e0_address;
}

TEST(PrestateTracer, pre_state_to_json)
{
    Account const a{.balance = 1000, .code_hash = A_CODE_HASH, .nonce = 1};
    OriginalAccountState as{a};
    as.storage_ = as.storage_.insert({key1, value1});
    as.storage_ = as.storage_.insert({key2, value2});
    as.storage_ = as.storage_.insert({key3, value3});

    trace::Map<Address, OriginalAccountState> prestate{};
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

TEST(PrestateTracer, zero_nonce)
{
    Account const a{.balance = 1000, .code_hash = NULL_HASH, .nonce = 0};
    OriginalAccountState as{a};

    trace::Map<Address, OriginalAccountState> prestate{};
    prestate.emplace(ADDR_A, as);

    // The State setup is only used to get code
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, StateDeltas{}, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "0x0000000000000000000000000000000000000100":{
            "balance":"0x3e8"
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
        "pre":{}
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas, s), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, statediff_account_creation)
{
    Account a{.balance = 500, .code_hash = A_CODE_HASH, .nonce = 1};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas{
        {ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}};

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
                "nonce":1
            }
        },
        "pre":{}
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas, s), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, statediff_balance_nonce_update)
{
    Account a{.balance = 500, .code_hash = A_CODE_HASH, .nonce = 1};
    Account b = a;
    b.nonce += 1;
    b.balance -= 100;

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas{
        {ADDR_A, StateDelta{.account = {a, b}, .storage = {}}}};

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
                "balance":"0x190",
                "nonce":2
            }
        },
        "pre":{
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x1f4",
                "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
                "nonce":1
            }
        }
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas, s), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, statediff_delete_storage)
{
    Account const a{.balance = 500, .code_hash = A_CODE_HASH, .nonce = 1};
    Account b = a;
    b.nonce += 1;
    b.balance -= 100;

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas1{
        {ADDR_A,
         StateDelta{
             .account = {a, b}, .storage = {{key1, {bytes32_t{}, value1}}}}}};

    StateDeltas state_deltas2{
        {ADDR_A,
         StateDelta{
             .account = {a, b}, .storage = {{key1, {value1, bytes32_t{}}}}}}};

    commit_sequential(
        tdb,
        state_deltas1,
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    commit_sequential(tdb, state_deltas2, Code{}, BlockHeader{.number = 1});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "post":{
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x190",
                "nonce":2
            }
        },
        "pre":{
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x1f4",
                "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
                "nonce":1,
                "storage":{
                    "0x00000000000000000000000000000000000000000000000000000000cafebabe": "0x0000000000000000000000000000000000000000000000000000000000000003"
                }
            }
        }
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas2, s),
        nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, statediff_multiple_fields_update)
{
    Account a{.balance = 500, .code_hash = A_CODE_HASH, .nonce = 1};
    Account b{.balance = 42, .code_hash = B_CODE_HASH, .nonce = 2};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas{
        {ADDR_A,
         StateDelta{
             .account = {a, b},
             .storage =
                 {
                     {key1, {value1, value2}},
                     {key2, {value2, value3}},
                 }}},
    };

    commit_sequential(
        tdb,
        state_deltas,
        Code{{A_CODE_HASH, A_ICODE}, {B_CODE_HASH, B_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "post":{
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x2a",
                "code":"0x60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
                "nonce":2,
                "storage":{
                    "0x00000000000000000000000000000000000000000000000000000000cafebabe":"0x0000000000000000000000000000000000000000000000000000000000000007",
                    "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c":"0x000000000000000000000000000000000000000000000000000000000000000a"
                }
            }
        },
        "pre":{
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x1f4",
                "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
                "nonce":1,
                "storage":{
                    "0x00000000000000000000000000000000000000000000000000000000cafebabe":"0x0000000000000000000000000000000000000000000000000000000000000003",
                    "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c":"0x0000000000000000000000000000000000000000000000000000000000000007"
                }
            }
        }
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas, s), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, statediff_account_deletion)
{
    Account a{.balance = 32, .code_hash = NULL_HASH, .nonce = 1};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas1{
        {ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}},
    };

    commit_sequential(tdb, state_deltas1, Code{}, BlockHeader{.number = 0});

    StateDeltas state_deltas2{
        {ADDR_A, StateDelta{.account = {a, std::nullopt}, .storage = {}}},
    };

    commit_sequential(tdb, state_deltas2, Code{}, BlockHeader{.number = 1});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "post":{
        },
        "pre":{
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x20",
                "nonce":1
            }
        }
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas2, s),
        nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, geth_example_prestate)
{
    // The only difference between this test and the Geth prestate tracer
    // example is the code/codehash. Here we use one from our test resources,
    // because the code in the Geth example is truncated.
    Account const a{.balance = 0, .code_hash = A_CODE_HASH, .nonce = 1};
    OriginalAccountState as{a};
    as.storage_ = as.storage_.insert({key4, value4});
    as.storage_ = as.storage_.insert({key5, value5});
    as.storage_ = as.storage_.insert({key6, value6});
    as.storage_ = as.storage_.insert({key7, value7});

    Account const b{
        .balance = 0x7a48734599f7284, .code_hash = NULL_HASH, .nonce = 1133};
    OriginalAccountState bs{b};
    Account const c{
        .balance = intx::from_string<uint256_t>("0x2638035a26d133809"),
        .code_hash = NULL_HASH,
        .nonce = 0};
    OriginalAccountState cs{c};
    Account const d{.balance = 0x0, .code_hash = NULL_HASH, .nonce = 0};
    OriginalAccountState ds{d};

    trace::Map<Address, OriginalAccountState> prestate{};
    prestate.emplace(addr1, ds);
    prestate.emplace(addr2, cs);
    prestate.emplace(addr3, bs);
    prestate.emplace(addr4, as);

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

    BlockState bs0(tdb, vm);
    State s(bs0, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "0x0000000000000000000000000000000000000002":{
            "balance":"0x0"
        },
        "0x008b3b2f992c0e14edaa6e2c662bec549caa8df1":{
            "balance":"0x2638035a26d133809"
        },
        "0x35a9f94af726f07b5162df7e828cc9dc8439e7d0":{
            "balance":"0x7a48734599f7284",
            "nonce":1133
        },
        "0xc8ba32cab1757528daf49033e3673fae77dcf05d":{
            "balance":"0x0",
            "code":"0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500",
            "nonce":1,
            "storage": {
                "0x0000000000000000000000000000000000000000000000000000000000000000":"0x000000000000000000000000000000000000000000000000000000000024aea6",
                "0x59fb7853eb21f604d010b94c123acbeae621f09ce15ee5d7616485b1e78a72e9":"0x00000000000000c42b56a52aedf18667c8ae258a0280a8912641c80c48cd9548",
                "0x8d8ebb65ec00cb973d4fe086a607728fd1b9de14aa48208381eed9592f0dee9a":"0x00000000000000784ae4881e40b1f5ebb4437905fbb8a5914454123b0293b35f",
                "0xff896b09014882056009dedb136458f017fcef9a4729467d0d00b4fd413fb1f1":"0x000000000000000e78ac39cb1c20e9edc753623b153705d0ccc487e31f9d6749"
            }
        }
    })";

    EXPECT_EQ(state_to_json(prestate, s), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, geth_example_statediff)
{
    Account const a{
        .balance = 0x7a48429e177130a, .code_hash = NULL_HASH, .nonce = 1134};
    Account const b{
        .balance = 0x7a48429e177130a, .code_hash = NULL_HASH, .nonce = 1135};

    StateDeltas state_deltas{
        {addr3, StateDelta{.account = {a, b}, .storage = {}}},
    };

    // The State setup is only used to get code
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs0(tdb, vm);
    State s(bs0, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "post":{
            "0x35a9f94af726f07b5162df7e828cc9dc8439e7d0":{
                "nonce":1135
            }
        },
        "pre":{
            "0x35a9f94af726f07b5162df7e828cc9dc8439e7d0":{
                "balance":"0x7a48429e177130a",
                "nonce":1134
            }
        }
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas, s), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, prestate_empty)
{
    trace::Map<Address, OriginalAccountState> prestate{};

    // The State setup is only used to get code
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, {}, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"({})";

    EXPECT_EQ(state_to_json(prestate, s), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, statediff_empty)
{
    StateDeltas state_deltas{};

    // The State setup is only used to get code
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "post":{
        },
        "pre":{
        }
    })";

    EXPECT_EQ(
        state_deltas_to_json(state_deltas, s), nlohmann::json::parse(json_str));
}

TYPED_TEST(TraitsTest, access_list_empty)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    nlohmann::json storage;
    auto const authorities = std::vector<std::optional<Address>>{};
    AccessListTracer tracer{storage, addr1, addr2, std::nullopt, authorities};
    tracer.encode<typename TestFixture::Trait>(s);

    EXPECT_EQ(storage, nlohmann::json::parse("[]"));
}

TYPED_TEST(TraitsTest, access_list_write)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    s.create_account_no_rollback(addr1);
    s.create_account_no_rollback(addr2);
    s.create_account_no_rollback(addr3);

    s.access_storage(addr2, key1);
    s.access_storage(addr2, key2);
    s.access_storage(addr3, key3);

    nlohmann::json storage;
    auto const authorities = std::vector<std::optional<Address>>{};
    auto const to = std::optional<Address>{addr5};
    AccessListTracer tracer{storage, addr1, addr4, to, authorities};
    tracer.encode<typename TestFixture::Trait>(s);

    auto const json_str = R"(
        [
            {
                "address": "0x008b3b2f992c0e14edaa6e2c662bec549caa8df1",
                "storageKeys": [
                    "0x00000000000000000000000000000000000000000000000000000000cafebabe",
                    "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c"
                ]
            },
            {
                "address": "0x35a9f94af726f07b5162df7e828cc9dc8439e7d0",
                "storageKeys": [
                    "0x5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b"
                ]
            }
        ]
    )";

    EXPECT_EQ(storage, nlohmann::json::parse(json_str));
}

TYPED_TEST(TraitsTest, access_list_regular_account)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    // Regular account is included even if it does not have storage keys set
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);
        s.create_account_no_rollback(addr4);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        auto const json_str = R"(
            [
                {
                    "address" : "0xc8ba32cab1757528daf49033e3673fae77dcf05d",
                    "storageKeys": []
                }
            ]
        )";

        EXPECT_EQ(storage, nlohmann::json::parse(json_str));
    }

    // Regular account is included if it has storage keys sets
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);
        s.create_account_no_rollback(addr4);

        s.access_storage(addr4, key1);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        auto const json_str = R"(
            [
                {
                    "address" : "0xc8ba32cab1757528daf49033e3673fae77dcf05d",
                    "storageKeys": [
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe"
                    ]
                }
            ]
        )";

        EXPECT_EQ(storage, nlohmann::json::parse(json_str));
    }
}

TYPED_TEST(TraitsTest, access_list_sender)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    // Sender is excluded if it does not have storage keys set
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        EXPECT_EQ(storage, nlohmann::json::parse("[]"));
    }

    // Sender is included if it has storage keys sets
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);

        s.access_storage(addr1, key1);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        auto const json_str = R"(
            [
                {
                    "address" : "0x0000000000000000000000000000000000000002",
                    "storageKeys": [
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe"
                    ]
                }
            ]
        )";

        EXPECT_EQ(storage, nlohmann::json::parse(json_str));
    }
}

TYPED_TEST(TraitsTest, access_list_beneficiary)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    // Beneficiary is excluded if it does not have storage keys set
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        EXPECT_EQ(storage, nlohmann::json::parse("[]"));
    }

    // Beneficiary is included if it has storage keys sets
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);

        s.access_storage(addr2, key1);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        auto const json_str = R"(
            [
                {
                    "address" : "0x008b3b2f992c0e14edaa6e2c662bec549caa8df1",
                    "storageKeys": [
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe"
                    ]
                }
            ]
        )";

        EXPECT_EQ(storage, nlohmann::json::parse(json_str));
    }
}

TYPED_TEST(TraitsTest, access_list_recipient)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    // Recipient is excluded if it does not have storage keys set
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        EXPECT_EQ(storage, nlohmann::json::parse("[]"));
    }

    // Recipient is included if it has storage keys sets
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);

        s.access_storage(addr3, key1);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        auto const json_str = R"(
            [
                {
                    "address" : "0x35a9f94af726f07b5162df7e828cc9dc8439e7d0",
                    "storageKeys": [
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe"
                    ]
                }
            ]
        )";

        EXPECT_EQ(storage, nlohmann::json::parse(json_str));
    }
}

TYPED_TEST(TraitsTest, access_list_authorities)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    // Valid authorities are excluded if they do not have storage keys set
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);
        s.create_account_no_rollback(addr4);
        s.create_account_no_rollback(addr5);

        nlohmann::json storage;
        auto const authorities =
            std::vector<std::optional<Address>>{addr4, addr5};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        EXPECT_EQ(storage, nlohmann::json::parse("[]"));
    }

    // Valid authorities are included if they have storage keys set
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);
        s.create_account_no_rollback(addr4);
        s.create_account_no_rollback(addr5);

        s.access_storage(addr4, key1);
        s.access_storage(addr5, key2);

        nlohmann::json storage;
        auto const authorities =
            std::vector<std::optional<Address>>{addr4, addr5};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        auto const json_str = R"(
            [
                {
                    "address" : "0xc8ba32cab1757528daf49033e3673fae77dcf05d",
                    "storageKeys": [
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe"
                    ]
                },
                {
                    "address" : "0xe02ad958162c9acb9c3eb90f67b02db21b10d3e0",
                    "storageKeys" : [
                        "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c"
                    ]
                }
            ]
        )";

        EXPECT_EQ(storage, nlohmann::json::parse(json_str));
    }
}

TYPED_TEST(TraitsTest, access_list_precompiles)
{
    StateDeltas state_deltas{};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, state_deltas, Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    constexpr auto ecrecover =
        0x0000000000000000000000000000000000000001_address;
    constexpr auto bls_g1_add =
        0x000000000000000000000000000000000000000b_address;

    auto const json_string = [] {
        if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
            return R"(
                    [
                        {
                            "address" : "0x000000000000000000000000000000000000000b",
                            "storageKeys": []
                        }
                    ]
                )";
        }
        else {
            return "[]";
        }
    }();

    // Precompiles are always excluded, depending on the active revision
    {
        State s{bs, Incarnation{0, 0}};

        s.create_account_no_rollback(addr1);
        s.create_account_no_rollback(addr2);
        s.create_account_no_rollback(addr3);
        s.create_account_no_rollback(ecrecover);
        s.create_account_no_rollback(bls_g1_add);

        nlohmann::json storage;
        auto const authorities = std::vector<std::optional<Address>>{};
        auto const to = std::optional<Address>{addr3};
        AccessListTracer tracer{storage, addr1, addr2, to, authorities};
        tracer.encode<typename TestFixture::Trait>(s);

        EXPECT_EQ(storage, nlohmann::json::parse(json_string));
    }
}
