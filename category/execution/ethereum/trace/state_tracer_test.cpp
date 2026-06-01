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

#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/evm.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance.hpp>
#include <monad/test/traits_test.hpp>

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <ankerl/unordered_dense.h>
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <test_resource_data.h>

#include <bit>
#include <optional>
#include <vector>

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb, sd({}), Code{{A_CODE_HASH, A_ICODE}}, BlockHeader{.number = 0});

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

    EXPECT_EQ(
        state_to_json(prestate, s, std::nullopt),
        nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, zero_nonce)
{
    Account const a{.balance = 1000, .code_hash = NULL_HASH, .nonce = 0};
    OriginalAccountState as{a};

    trace::Map<Address, OriginalAccountState> prestate{};
    prestate.emplace(ADDR_A, as);

    // The State setup is only used to get code
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"(
    {
        "0x0000000000000000000000000000000000000100":{
            "balance":"0x3e8"
        }
        
    })";

    EXPECT_EQ(
        state_to_json(prestate, s, std::nullopt),
        nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, state_deltas_to_json)
{
    Account a{.balance = 500, .code_hash = A_CODE_HASH, .nonce = 1};

    mpt::Db db{std::make_unique<InMemoryMachine>()};
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
        sd(state_deltas),
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

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas{
        {ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}};

    commit_sequential(
        tdb,
        sd(state_deltas),
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

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas{
        {ADDR_A, StateDelta{.account = {a, b}, .storage = {}}}};

    commit_sequential(
        tdb,
        sd(state_deltas),
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

    mpt::Db db{std::make_unique<InMemoryMachine>()};
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
        sd(state_deltas1),
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    commit_sequential(tdb, sd(state_deltas2), Code{}, BlockHeader{.number = 1});

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

    mpt::Db db{std::make_unique<InMemoryMachine>()};
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
        sd(state_deltas),
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

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    StateDeltas state_deltas1{
        {ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}},
    };

    commit_sequential(tdb, sd(state_deltas1), Code{}, BlockHeader{.number = 0});

    StateDeltas state_deltas2{
        {ADDR_A, StateDelta{.account = {a, std::nullopt}, .storage = {}}},
    };

    commit_sequential(tdb, sd(state_deltas2), Code{}, BlockHeader{.number = 1});

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
        .balance = uint256_t::from_string("0x2638035a26d133809"),
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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb, sd({}), Code{{A_CODE_HASH, A_ICODE}}, BlockHeader{.number = 0});

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

    EXPECT_EQ(
        state_to_json(prestate, s, std::nullopt),
        nlohmann::json::parse(json_str));
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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd(state_deltas), Code{}, BlockHeader{.number = 0});

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    auto const json_str = R"({})";

    EXPECT_EQ(
        state_to_json(prestate, s, Address{}), nlohmann::json::parse(json_str));
}

TEST(PrestateTracer, statediff_empty)
{
    StateDeltas state_deltas{};

    // The State setup is only used to get code
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd(state_deltas), Code{}, BlockHeader{.number = 0});

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

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd(state_deltas), Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    nlohmann::json storage;
    auto const authorities = std::vector<std::optional<Address>>{};
    AccessListTracer tracer{storage, addr1, addr2, std::nullopt, authorities};
    tracer.encode<typename TestFixture::Trait>(s);

    EXPECT_EQ(storage, nlohmann::json::parse("[]"));
}

TYPED_TEST(TraitsTest, access_list_state_view_excludes_rejected_frame)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    s.push();
    s.access_storage(addr4, key4);
    s.pop_reject();

    nlohmann::json storage;
    auto const authorities = std::vector<std::optional<Address>>{};
    AccessListTracer tracer{storage, addr1, addr2, std::nullopt, authorities};
    tracer.encode<typename TestFixture::Trait>(s);

    // Rejected frames must not leak accessed storage back into State. RPC
    // access-list observability needs to be handled by tracer-specific capture.
    EXPECT_EQ(storage, nlohmann::json::parse("[]"));
}

TYPED_TEST(TraitsTest, access_list_records_rejected_frame_storage)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    nlohmann::json storage;
    auto const authorities = std::vector<std::optional<Address>>{};
    StateTracer tracer =
        AccessListTracer{storage, addr1, addr2, std::nullopt, authorities};

    s.push();
    s.access_storage(addr4, key4);
    on_frame_reject(tracer, s);
    s.pop_reject();

    run_tracer<typename TestFixture::Trait>(tracer, s);

    auto const json_str = R"(
        [
            {
                "address" : "0xc8ba32cab1757528daf49033e3673fae77dcf05d",
                "storageKeys": [
                    "0x0000000000000000000000000000000000000000000000000000000000000000"
                ]
            }
        ]
    )";

    EXPECT_EQ(storage, nlohmann::json::parse(json_str));
}

TYPED_TEST(TraitsTest, access_list_records_rejected_frame_regular_account)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    nlohmann::json storage;
    auto const authorities = std::vector<std::optional<Address>>{};
    StateTracer tracer =
        AccessListTracer{storage, addr1, addr2, std::nullopt, authorities};

    s.push();
    s.access_account(addr4);
    on_frame_reject(tracer, s);
    s.pop_reject();

    run_tracer<typename TestFixture::Trait>(tracer, s);

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

TYPED_TEST(TraitsTest, access_list_write)
{
    StateDeltas state_deltas{};

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd(state_deltas), Code{}, BlockHeader{.number = 0});

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

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
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(tdb, sd({}), Code{}, BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    constexpr auto ecrecover =
        0x0000000000000000000000000000000000000001_address;
    constexpr auto bls_g1_add =
        0x000000000000000000000000000000000000000b_address;

    auto const json_string = [] {
        if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_PRAGUE) {
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

TEST(PrestateTracer, prestate_access_storage)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, a},
                  .storage = {StorageDeltas{
                      {key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}}}),
        {},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    State s(bs, Incarnation{0, 0});

    // Touch some of the account's storage.
    // First access the account to bring it into the state object; this is a
    // prerequisite for accessing the storage.
    EXPECT_EQ(s.access_account(ADDR_A), EVMC_ACCESS_COLD);
    EXPECT_TRUE(s.original().find(ADDR_A) != s.original().end());
    EXPECT_TRUE(s.current().find(ADDR_A) != s.current().end());
    EXPECT_EQ(s.get_storage(ADDR_A, key2), value2);
    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = R"(
        {
            "0x0000000000000000000000000000000000000100": {
                "balance": "0x0",
                "nonce": 1,
                "storage": {
                    "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c": "0x0000000000000000000000000000000000000000000000000000000000000007"
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        // We only read the storage, so no changes are recorded in the
        // statediff.
        auto const json_str = R"(
        {
            "post": {},
            "pre": {}
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

TEST(PrestateTracer, prestate_retain_beneficiary_set_storage)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd({{ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}}),
        {},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    // Modify the storage of the beneficiary, which implies it must show up in
    // the prestate trace.
    s.set_storage(ADDR_A, key1, value1);

    {
        // Run pretracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = R"(
        {
            "0x0000000000000000000000000000000000000100":{
                "balance": "0x0",
                "nonce": 1
            }

        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        auto const json_str = R"(
        {
            "post": {
                "0x0000000000000000000000000000000000000100": {
                    "storage": {
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe": "0x0000000000000000000000000000000000000000000000000000000000000003"
                    }
                }
            },
            "pre": {
                "0x0000000000000000000000000000000000000100": {
                    "balance": "0x0",
                    "nonce": 1
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

TEST(PrestateTracer, prestate_retain_beneficiary_modified_storage)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, a},
                  .storage = {{key1, {bytes32_t{}, value1}}}}}}),
        {},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    // Modify the storage of the beneficiary, which implies it must show up
    // in the prestate trace.
    s.set_storage(ADDR_A, key1, value2);

    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = R"(
        {
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x0",
                "nonce":1,
                "storage":{
                    "0x00000000000000000000000000000000000000000000000000000000cafebabe": "0x0000000000000000000000000000000000000000000000000000000000000003"
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        auto const json_str = R"(
        {
            "post": {
                "0x0000000000000000000000000000000000000100": {
                    "storage": {
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe": "0x0000000000000000000000000000000000000000000000000000000000000007"
                    }
                }
            },
            "pre": {
                "0x0000000000000000000000000000000000000100": {
                    "balance":"0x0",
                    "nonce":1,
                    "storage":{
                        "0x00000000000000000000000000000000000000000000000000000000cafebabe": "0x0000000000000000000000000000000000000000000000000000000000000003"
                    }
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

TEST(PrestateTracer, prestate_retain_beneficiary_modified_balance)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd({{ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}}),
        {},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    // Modify the balance of the beneficiary, which implies it
    // must show up in the prestate trace.
    s.add_to_balance(ADDR_A, uint256_t{42});

    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};

        // Run tracer
        tracer.encode(s.original(), s);

        auto const json_str = R"(
        {
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x0",
                "nonce":1
            }

        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};

        // Run tracer
        tracer.encode(tracer.trace(s), s);

        auto const json_str = R"(
        {
            "post": {
                "0x0000000000000000000000000000000000000100":{
                    "balance": "0x2a"
                }
            },
            "pre": {
                "0x0000000000000000000000000000000000000100":{
                    "balance":"0x0",
                    "nonce":1
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

TEST(PrestateTracer, prestate_retain_beneficiary_modified_nonce)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd({{ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}}),
        {},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    // Modify the nonce of the beneficiary, which implies it
    // must show up in the prestate trace.
    s.set_nonce(ADDR_A, 2);

    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = R"(
        {
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x0",
                "nonce":1
            }

        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        auto const json_str = R"(
        {
            "post": {
                "0x0000000000000000000000000000000000000100": {
                    "nonce": 2
                }
            },
            "pre": {
                "0x0000000000000000000000000000000000000100": {
                    "balance": "0x0",
                    "nonce": 1
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

TEST(PrestateTracer, prestate_retain_beneficiary_modified_code_hash)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd({{ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}}),
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    State s(bs, Incarnation{0, 0});

    // Re-setting beneficiary code marks account as modified and
    // must show up in the prestate trace.
    s.set_code(ADDR_A, A_CODE);

    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = R"(
        {
            "0x0000000000000000000000000000000000000100":{
                "balance":"0x0",
                "nonce":1
            }

        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        auto const json_str = R"(
        {
            "post": {
                "0x0000000000000000000000000000000000000100": {
                    "code": "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500"
                }
            },
            "pre": {
                "0x0000000000000000000000000000000000000100":{
                    "balance":"0x0",
                    "nonce":1
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

// Similar to `prestate_access_storage`, but tests that the beneficiary is not
// erroneously omitted.
TEST(PrestateTracer, prestate_retain_beneficiary_access_storage)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd(
            {{ADDR_A,
              StateDelta{
                  .account = {std::nullopt, a},
                  .storage = {StorageDeltas{
                      {key1, {bytes32_t{}, value1}},
                      {key2, {bytes32_t{}, value2}}}}}}}),
        {},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    State s(bs, Incarnation{0, 0});

    // Touch some of the account's storage.
    // First access the account to bring it into the state object; this is a
    // prerequisite for accessing the storage.
    EXPECT_EQ(s.access_account(ADDR_A), EVMC_ACCESS_COLD);
    EXPECT_TRUE(s.original().find(ADDR_A) != s.original().end());
    EXPECT_TRUE(s.current().find(ADDR_A) != s.current().end());
    EXPECT_EQ(s.get_storage(ADDR_A, key2), value2);
    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = R"(
        {
            "0x0000000000000000000000000000000000000100": {
                "balance": "0x0",
                "nonce": 1,
                "storage": {
                    "0x1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c1c": "0x0000000000000000000000000000000000000000000000000000000000000007"
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        // We only read the storage, so no changes are recorded in the
        // statediff.
        auto const json_str = R"(
        {
            "post": {},
            "pre": {}
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

TEST(PrestateTracer, prestate_omit_beneficiary)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    Account const a{.balance = 0, .nonce = 1};

    // Block 0
    commit_sequential(
        tdb,
        sd({{ADDR_A, StateDelta{.account = {std::nullopt, a}, .storage = {}}}}),
        {},
        BlockHeader{.number = 0});

    BlockState bs(tdb, vm);

    State s(bs, Incarnation{0, 0});

    // Touch the account, so it shows up in `state.original` and
    // `state.current`.
    EXPECT_EQ(s.access_account(ADDR_A), EVMC_ACCESS_COLD);
    EXPECT_TRUE(s.original().find(ADDR_A) != s.original().end());
    EXPECT_TRUE(s.current().find(ADDR_A) != s.current().end());

    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = "null";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        auto const json_str = R"(
        {
            "post": {},
            "pre": {}
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

TEST(PrestateTracer, prestate_empty_block_no_reward)
{
    // Setup matter
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    BlockHeader header{.number = 0, .beneficiary = ADDR_A};
    Block const block{header, {}, {}};

    // Block 0
    commit_sequential(tdb, sd({}), {}, header);

    BlockState bs(tdb, vm);
    State s(bs, Incarnation{0, 0});

    // Apply block reward.
    apply_block_reward<MonadTraits<MONAD_NEXT>>(s, block);
    EXPECT_TRUE(s.original().find(ADDR_A) == s.original().end());
    EXPECT_TRUE(s.current().find(ADDR_A) == s.current().end());

    {
        // Run prestate tracer
        nlohmann::json trace;
        trace::PrestateTracer tracer{trace, ADDR_A};
        tracer.encode(s.original(), s);

        auto const json_str = "null";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }

    {
        // Run statediff tracer
        nlohmann::json trace;
        trace::StateDiffTracer tracer{trace};
        tracer.encode(tracer.trace(s), s);

        auto const json_str = R"(
        {
            "post": {},
            "pre": {}
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(json_str));
    }
}

// CodeTracer coverage.
//
// Each test below constructs `StateTracer{CodeTracer{}}`, exercises exactly
// one of the `on_read_code` recording sites in the execution layer, and
// asserts that the recorded codes map contains the (code_hash, intercode)
// pair that the site is responsible for. The sites are:
//
//   1. EvmcHostBase::get_code_size  (EXTCODESIZE host hook)
//   2. EvmcHostBase::copy_code       (EXTCODECOPY host hook)
//   3. execute_call_message          (called contract code, per CALL)
//   4. system_call (via process_requests, EIP-7002/7251)
//   5. validate_ethereum_transaction (EIP-7702 sender code check)
//   6. process_authorizations        (EIP-7702 authority code check)
//   7. dipped_into_reserve + is_delegated (Monad reserve-balance revert path)
//
// Without these, future changes to any site can silently drop a code preimage
// from the witness without CI catching it.

namespace
{
    // EIP-7002/7251 predeploy addresses + a trivial system contract stub
    // (single STOP opcode) used by the process_requests test below.
    constexpr auto WITHDRAWAL_REQUEST_ADDRESS =
        0x00000961ef480eb55e80d19ad83579a64c007002_address;
    constexpr auto CONSOLIDATION_REQUEST_ADDRESS =
        0x0000bbddc7ce488642fb579f8b00f3a590007251_address;
    inline auto const SYSTEM_STUB_CODE = monad::from_hex("00").value();
    inline auto const SYSTEM_STUB_CODE_HASH =
        to_bytes(monad::keccak256(SYSTEM_STUB_CODE));
    inline auto const SYSTEM_STUB_ICODE =
        monad::vm::make_shared_intercode(SYSTEM_STUB_CODE);
}

// Site 1: EvmcHostBase::get_code_size
TYPED_TEST(TraitsTest, code_tracer_records_extcodesize)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        sd(
            {{ADDR_A,
              StateDelta{
                  .account =
                      {std::nullopt, Account{.code_hash = A_CODE_HASH}}}}}),
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};

    NoopCallTracer call_tracer;
    BlockHashBufferFinalized const block_hash_buffer;
    Transaction const tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t const base_fee{0};
    trace::StateTracer state_tracer = trace::CodeTracer{};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer,
        state_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        tx,
        base_fee,
        0,
        chain_ctx};

    EXPECT_EQ(host.get_code_size(ADDR_A), A_ICODE->size());

    auto const &codes = std::get<trace::CodeTracer>(state_tracer).codes;
    EXPECT_EQ(codes.size(), 1u);
    auto const it = codes.find(A_CODE_HASH);
    ASSERT_TRUE(it != codes.end());
    EXPECT_EQ(
        byte_string_view(it->second->code(), it->second->size()),
        byte_string_view(A_ICODE->code(), A_ICODE->size()));
}

// Site 2: EvmcHostBase::copy_code
TYPED_TEST(TraitsTest, code_tracer_records_extcodecopy)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        sd(
            {{ADDR_A,
              StateDelta{
                  .account =
                      {std::nullopt, Account{.code_hash = A_CODE_HASH}}}}}),
        Code{{A_CODE_HASH, A_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};

    NoopCallTracer call_tracer;
    BlockHashBufferFinalized const block_hash_buffer;
    Transaction const tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t const base_fee{0};
    trace::StateTracer state_tracer = trace::CodeTracer{};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer,
        state_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        tx,
        base_fee,
        0,
        chain_ctx};

    std::vector<uint8_t> buf(A_ICODE->size(), 0);
    auto const n = host.copy_code(ADDR_A, 0, buf.data(), buf.size());
    EXPECT_EQ(n, A_ICODE->size());
    EXPECT_TRUE(std::equal(
        buf.begin(),
        buf.begin() + static_cast<std::ptrdiff_t>(n),
        A_ICODE->code()));

    auto const &codes = std::get<trace::CodeTracer>(state_tracer).codes;
    EXPECT_EQ(codes.size(), 1u);
    auto const it = codes.find(A_CODE_HASH);
    ASSERT_TRUE(it != codes.end());
    EXPECT_EQ(
        byte_string_view(it->second->code(), it->second->size()),
        byte_string_view(A_ICODE->code(), A_ICODE->size()));
}

// Site 3: execute_call_message records called-contract code
TYPED_TEST(TraitsTest, code_tracer_records_called_contract_code)
{
    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        sd({{ADDR_A,
             StateDelta{
                 .account =
                     {std::nullopt, Account{.balance = 10'000'000'000}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {std::nullopt, Account{.code_hash = B_CODE_HASH}}}}}),
        Code{{B_CODE_HASH, B_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};

    NoopCallTracer call_tracer;
    BlockHashBufferFinalized const block_hash_buffer;
    Transaction const tx{};
    auto const chain_ctx =
        ChainContext<typename TestFixture::Trait>::debug_empty();
    uint256_t const base_fee{0};
    trace::StateTracer state_tracer = trace::CodeTracer{};
    EvmcHost<typename TestFixture::Trait> host{
        call_tracer,
        state_tracer,
        EMPTY_TX_CONTEXT,
        block_hash_buffer,
        state,
        tx,
        base_fee,
        0,
        chain_ctx};

    // depth = 1 to bypass the depth-0 reserve-balance revert path; we want
    // to isolate execute_call_message's own code-read here.
    auto msg_memory = vm.message_memory_ref();
    evmc_message const msg{
        .kind = EVMC_CALL,
        .depth = 1,
        .gas = 1'000'000,
        .recipient = ADDR_B,
        .sender = ADDR_A,
        .code_address = ADDR_B,
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = vm.message_memory_capacity(),
    };

    (void)execute_call_message<typename TestFixture::Trait>(&host, state, msg);

    auto const &codes = std::get<trace::CodeTracer>(state_tracer).codes;
    auto const it = codes.find(B_CODE_HASH);
    ASSERT_TRUE(it != codes.end())
        << "called contract code not recorded by execute_call_message";
    EXPECT_EQ(
        byte_string_view(it->second->code(), it->second->size()),
        byte_string_view(B_ICODE->code(), B_ICODE->size()));
}

// Site 4: system_call (via process_requests) records system-contract code
TYPED_TEST(TraitsTest, code_tracer_records_system_contract_code)
{
    if constexpr (!TestFixture::Trait::eip_7685_active()) {
        GTEST_SKIP() << "process_requests requires EIP-7685";
    }
    else {
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm;

        commit_sequential(
            tdb,
            sd({{WITHDRAWAL_REQUEST_ADDRESS,
                 StateDelta{
                     .account =
                         {std::nullopt,
                          Account{.code_hash = SYSTEM_STUB_CODE_HASH}}}},
                {CONSOLIDATION_REQUEST_ADDRESS,
                 StateDelta{
                     .account =
                         {std::nullopt,
                          Account{.code_hash = SYSTEM_STUB_CODE_HASH}}}}}),
            Code{{SYSTEM_STUB_CODE_HASH, SYSTEM_STUB_ICODE}},
            BlockHeader{.number = 0});

        BlockState bs{tdb, vm};
        State state{bs, Incarnation{0, 0}};

        BlockHashBufferFinalized const block_hash_buffer;
        BlockHeader const header{};
        EthereumMainnet const chain;
        auto const chain_ctx =
            ChainContext<typename TestFixture::Trait>::debug_empty();
        trace::StateTracer state_tracer = trace::CodeTracer{};

        auto const result = process_requests<typename TestFixture::Trait>(
            chain,
            state,
            block_hash_buffer,
            header,
            state_tracer,
            chain_ctx,
            std::span<Receipt const>{});
        ASSERT_TRUE(result.has_value());

        auto const &codes = std::get<trace::CodeTracer>(state_tracer).codes;
        auto const it = codes.find(SYSTEM_STUB_CODE_HASH);
        ASSERT_TRUE(it != codes.end())
            << "system contract code not recorded by system_call";
        EXPECT_EQ(
            byte_string_view(it->second->code(), it->second->size()),
            byte_string_view(
                SYSTEM_STUB_ICODE->code(), SYSTEM_STUB_ICODE->size()));
    }
}

// Site 5: validate_ethereum_transaction records sender code on EIP-7702 check
TYPED_TEST(TraitsTest, code_tracer_records_sender_code_in_validate)
{
    if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_PRAGUE) {
        GTEST_SKIP() << "EIP-7702 sender code read requires Prague+";
    }
    else {
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm;

        // Sender has non-empty code so the Prague+ branch reads it. The code
        // is not a delegation indicator, so validate returns SenderNotEoa,
        // but the read site still records --- which is the property under test.
        commit_sequential(
            tdb,
            sd(
                {{ADDR_A,
                  StateDelta{
                      .account =
                          {std::nullopt,
                           Account{
                               .balance = 100'000'000'000'000'000,
                               .code_hash = C_CODE_HASH}}}}}),
            Code{{C_CODE_HASH, C_ICODE}},
            BlockHeader{.number = 0});

        BlockState bs{tdb, vm};
        State state{bs, Incarnation{0, 0}};

        Transaction const tx{.gas_limit = 60'500};
        trace::StateTracer state_tracer = trace::CodeTracer{};
        (void)validate_ethereum_transaction<typename TestFixture::Trait>(
            tx, ADDR_A, state, state_tracer);

        auto const &codes = std::get<trace::CodeTracer>(state_tracer).codes;
        auto const it = codes.find(C_CODE_HASH);
        ASSERT_TRUE(it != codes.end())
            << "sender code not recorded by validate_ethereum_transaction";
        EXPECT_EQ(
            byte_string_view(it->second->code(), it->second->size()),
            byte_string_view(C_ICODE->code(), C_ICODE->size()));
    }
}

// Site 6: process_authorizations records authority code
//
// Goes through ExecuteTransactionNoValidation because process_authorizations
// is a private member. The authority's code (B_CODE) is neither empty nor a
// delegation indicator, so the entry is rejected after the read --- but the
// read site still records, which is what we assert.
//
// Restricted to Ethereum Prague+ to avoid having to construct a sized
// Monad-specific ChainContext for init_reserve_balance_context, which runs
// at the top of operator() for monad traits. The Monad MONAD_FOUR+ exercise
// of process_authorizations is structurally identical and is indirectly
// covered by the witness-generation integration tests.
TYPED_TEST(EvmTraitsTest, code_tracer_records_authorization_code)
{
    if constexpr (TestFixture::Trait::evm_rev() < MONAD_ETH_PRAGUE) {
        GTEST_SKIP() << "EIP-7702 authority code read requires Prague+";
    }
    else {
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm;

        commit_sequential(
            tdb,
            sd({{ADDR_A,
                 StateDelta{
                     .account =
                         {std::nullopt,
                          Account{
                              .balance = 100'000'000'000'000'000,
                              .nonce = 0}}}},
                {ADDR_B,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.code_hash = B_CODE_HASH}}}}}),
            Code{{B_CODE_HASH, B_ICODE}},
            BlockHeader{.number = 0});

        BlockState bs{tdb, vm};
        State state{bs, Incarnation{0, 0}};

        // One authorization entry whose authority is ADDR_B. The authorities
        // span shadows recovered addresses; we set it to ADDR_B directly,
        // sidestepping signature recovery.
        AuthorizationEntry auth{};
        auth.sc.chain_id = 0; // 0 always matches host_chain_id in step 1
        auth.nonce = 0;
        auth.address = ADDR_B;
        Transaction tx{
            .max_fee_per_gas = 1,
            .gas_limit = 100'000,
            .to = ADDR_B,
            .type = TransactionType::eip7702,
        };
        tx.authorization_list.push_back(auth);

        std::vector<std::optional<Address>> const authorities = {ADDR_B};

        NoopCallTracer call_tracer;
        BlockHashBufferFinalized const block_hash_buffer;
        auto const chain_ctx =
            ChainContext<typename TestFixture::Trait>::debug_empty();
        uint256_t const base_fee{0};
        trace::StateTracer state_tracer = trace::CodeTracer{};
        EvmcHost<typename TestFixture::Trait> host{
            call_tracer,
            state_tracer,
            EMPTY_TX_CONTEXT,
            block_hash_buffer,
            state,
            tx,
            base_fee,
            0,
            chain_ctx};

        (void)ExecuteTransactionNoValidation<typename TestFixture::Trait>{
            EthereumMainnet{}, tx, ADDR_A, authorities, BlockHeader{}}(
            state, host);

        auto const &codes = std::get<trace::CodeTracer>(state_tracer).codes;
        auto const it = codes.find(B_CODE_HASH);
        ASSERT_TRUE(it != codes.end())
            << "authority code not recorded by process_authorizations";
        EXPECT_EQ(
            byte_string_view(it->second->code(), it->second->size()),
            byte_string_view(B_ICODE->code(), B_ICODE->size()));
    }
}

// Sites 7+8: dipped_into_reserve and is_delegated (Monad MONAD_FOUR+).
//
// init_reserve_balance_context calls is_delegated for the sender, which
// reads and records the sender's code when sender_code_hash != NULL_HASH.
// revert_transaction -> dipped_into_reserve iterates state.current() and
// records each non-empty code there (the read happens before the
// is_delegated short-circuit, so non-delegated accounts are still recorded).
//
// We engineer the setup so each hash is attributable to exactly one site:
//   - A_CODE_HASH: only recorded via is_delegated (sender is NOT in current())
//   - B_CODE_HASH: only recorded via dipped_into_reserve (ADDR_B is in
//                  current() but is not the sender, so the is_delegated call
//                  above does not touch it).
TYPED_TEST(MonadTraitsTest, code_tracer_records_reserve_balance_code)
{
    using Trait = typename TestFixture::Trait;
    if (TestFixture::REV < MONAD_FOUR) {
        GTEST_SKIP() << "reserve-balance code reads are MONAD_FOUR+ only";
    }

    constexpr auto SENDER = 0x5353535353535353535353535353535353535353_address;

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;

    commit_sequential(
        tdb,
        sd({{SENDER,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 100'000'000'000'000'000,
                          .code_hash = A_CODE_HASH}}}},
            {ADDR_B,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 100'000, .code_hash = B_CODE_HASH}}}}}),
        Code{{A_CODE_HASH, A_ICODE}, {B_CODE_HASH, B_ICODE}},
        BlockHeader{.number = 0});

    BlockState bs{tdb, vm};
    State state{bs, Incarnation{0, 0}};

    // Bring ADDR_B into state.current() so dipped_into_reserve iterates it.
    // Sender is intentionally NOT accessed: init_reserve_balance_context's
    // is_delegated reads via state.get_code_hash / original_account_state,
    // neither of which inserts into current_.
    state.access_account(ADDR_B);

    ankerl::unordered_dense::segmented_set<Address> const empty_neighbours;
    std::vector<Address> const senders = {SENDER};
    std::vector<std::vector<std::optional<Address>>> const authorities = {{}};
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
    senders_and_authorities.insert(SENDER);
    ChainContext<Trait> const ctx{
        .grandparent_senders_and_authorities = empty_neighbours,
        .parent_senders_and_authorities = empty_neighbours,
        .senders_and_authorities = senders_and_authorities,
        .senders = senders,
        .authorities = authorities};

    Transaction const tx{.max_fee_per_gas = 1, .gas_limit = 21'000};
    trace::StateTracer state_tracer = trace::CodeTracer{};

    init_reserve_balance_context<Trait>(
        state,
        SENDER,
        tx,
        std::optional<uint256_t>{0},
        /*i=*/0,
        state_tracer,
        ctx);

    (void)revert_transaction<Trait>(
        SENDER, tx, /*base_fee_per_gas=*/0, /*i=*/0, state, state_tracer, ctx);

    auto const &codes = std::get<trace::CodeTracer>(state_tracer).codes;
    auto const it_a = codes.find(A_CODE_HASH);
    ASSERT_TRUE(it_a != codes.end())
        << "sender code not recorded by is_delegated";
    EXPECT_EQ(
        byte_string_view(it_a->second->code(), it_a->second->size()),
        byte_string_view(A_ICODE->code(), A_ICODE->size()));
    auto const it_b = codes.find(B_CODE_HASH);
    ASSERT_TRUE(it_b != codes.end())
        << "current()-iterated account code not recorded by "
           "dipped_into_reserve";
    EXPECT_EQ(
        byte_string_view(it_b->second->code(), it_b->second->size()),
        byte_string_view(B_ICODE->code(), B_ICODE->size()));
}
