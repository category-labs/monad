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
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/execute_system_transaction.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/traits_test.hpp>

#include <test_resource_data.h>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <cstdint>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::test;

TEST(SystemTransaction, prestate_trace_staking_epoch_change)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    MonadDevnet chain;

    BlockState block_state{tdb, vm};
    BlockMetrics block_metrics;

    BlockHeader const header{.number = 0};

    NoopCallTracer noop_call_tracer;

    // Create a system transaction that calls syscallOnEpochChange
    auto const epoch_change_tx = [](uint64_t tx_nonce,
                                    uint64_t next_epoch) -> Transaction {
        return Transaction{
            // Some arbitrary signature which is sufficient to pass
            // validation.
            .sc =
                SignatureAndChain{
                    .r = 1,
                    .s = 2,
                    .y_parity = 0,
                },
            .nonce = tx_nonce,
            .to = staking::STAKING_CA,
            .data = evmc::from_hex(std::format(
                                       "0x1d4e9f0200000000000000000000000000000"
                                       "0000000000000000000000000000000000{}",
                                       next_epoch))
                        .value()};
    };

    {
        nlohmann::json trace;
        trace::StateTracer prestate_tracer =
            trace::PrestateTracer{trace, 0xdeadbeef_address};

        // Fulfil this promise such that ExecuteSystemTransaction doesn't wait
        // indefinitely.
        boost::fibers::promise<void> promise;
        promise.set_value();

        Result<Receipt> const result =
            ExecuteSystemTransaction<MonadTraits<MONAD_NEXT>>{
                chain,
                0,
                epoch_change_tx(0, 1),
                SYSTEM_SENDER,
                header,
                block_state,
                block_metrics,
                promise,
                noop_call_tracer,
                prestate_tracer}();

        EXPECT_TRUE(result.has_value());

        auto const expected = R"({
            "0x0000000000000000000000000000000000001000": {
                "balance": "0x0"
            },
            "0x6f49a8f621353f12378d0046e7d7e4b9b249dc9e": {
                "balance": "0x0"
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(expected));
    }

    {
        nlohmann::json trace;
        trace::StateTracer prestate_tracer =
            trace::PrestateTracer{trace, 0xdeadbeef_address};

        boost::fibers::promise<void> promise;
        promise.set_value();

        Result<Receipt> const result =
            ExecuteSystemTransaction<MonadTraits<MONAD_NEXT>>{
                chain,
                1,
                epoch_change_tx(1, 2),
                SYSTEM_SENDER,
                header,
                block_state,
                block_metrics,
                promise,
                noop_call_tracer,
                prestate_tracer}();

        EXPECT_TRUE(result.has_value());

        auto const expected = R"({
            "0x0000000000000000000000000000000000001000": {
                "balance": "0x0",
                "storage": {
                    "0x0000000000000000000000000000000000000000000000000000000000000001": "0x0000000000000001000000000000000000000000000000000000000000000000"
                }
            },
            "0x6f49a8f621353f12378d0046e7d7e4b9b249dc9e": {
                "balance": "0x0",
                "nonce": 1
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(expected));
    }
}

TEST(SystemTransaction, statediff_trace_staking_epoch_change)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;

    MonadDevnet chain;

    BlockState block_state{tdb, vm};
    BlockMetrics block_metrics;

    BlockHeader const header{.number = 0};

    NoopCallTracer noop_call_tracer;

    auto const epoch_change_tx = [](uint64_t tx_nonce,
                                    uint64_t next_epoch) -> Transaction {
        return Transaction{
            .sc =
                SignatureAndChain{
                    .r = 1,
                    .s = 2,
                    .y_parity = 0,
                },
            .nonce = tx_nonce,
            .to = staking::STAKING_CA,
            .data = evmc::from_hex(std::format(
                                       "0x1d4e9f0200000000000000000000000000000"
                                       "0000000000000000000000000000000000{}",
                                       next_epoch))
                        .value()};
    };

    {
        nlohmann::json trace;
        trace::StateTracer statediff_tracer = trace::StateDiffTracer{trace};

        boost::fibers::promise<void> promise;
        promise.set_value();

        Result<Receipt> const result =
            ExecuteSystemTransaction<MonadTraits<MONAD_NEXT>>{
                chain,
                0,
                epoch_change_tx(0, 1),
                SYSTEM_SENDER,
                header,
                block_state,
                block_metrics,
                promise,
                noop_call_tracer,
                statediff_tracer}();

        EXPECT_TRUE(result.has_value());

        auto const expected = R"({
            "post": {
                "0x0000000000000000000000000000000000001000": {
                    "balance": "0x0",
                    "storage": {
                        "0x0000000000000000000000000000000000000000000000000000000000000001": "0x0000000000000001000000000000000000000000000000000000000000000000"
                    }
                },
                "0x6f49a8f621353f12378d0046e7d7e4b9b249dc9e": {
                    "balance": "0x0",
                    "nonce": 1
                }
            },
            "pre": {}
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(expected));
    }

    {
        nlohmann::json trace;
        trace::StateTracer statediff_tracer = trace::StateDiffTracer{trace};

        boost::fibers::promise<void> promise;
        promise.set_value();

        Result<Receipt> const result =
            ExecuteSystemTransaction<MonadTraits<MONAD_NEXT>>{
                chain,
                1,
                epoch_change_tx(1, 2),
                SYSTEM_SENDER,
                header,
                block_state,
                block_metrics,
                promise,
                noop_call_tracer,
                statediff_tracer}();

        EXPECT_TRUE(result.has_value());

        auto const expected = R"({
            "post": {
                "0x0000000000000000000000000000000000001000": {
                    "storage": {
                        "0x0000000000000000000000000000000000000000000000000000000000000001": "0x0000000000000002000000000000000000000000000000000000000000000000"
                    }
                },
                "0x6f49a8f621353f12378d0046e7d7e4b9b249dc9e": {
                    "nonce": 2
                }
            },
            "pre": {
                "0x0000000000000000000000000000000000001000": {
                    "balance": "0x0",
                    "storage": {
                        "0x0000000000000000000000000000000000000000000000000000000000000001": "0x0000000000000001000000000000000000000000000000000000000000000000"
                    }
                },
                "0x6f49a8f621353f12378d0046e7d7e4b9b249dc9e": {
                    "balance": "0x0",
                    "nonce": 1
                }
            }
        })";

        EXPECT_EQ(trace, nlohmann::json::parse(expected));
    }
}
