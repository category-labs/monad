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

#include <category/core/address.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/traits_test.hpp>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

using namespace monad;

TYPED_TEST(MonadTraitsTest, mip11_fork)
{
    using Trait = TestFixture::Trait;

    static constexpr Address from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr Address beneficiary{0xb0b0_address};
    static constexpr Address recipient{0xa1ce_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 1'000'000'000'000'000'000);
        bs.merge(state);
    }

    static constexpr uint64_t gas_limit = 21'000;
    static constexpr uint256_t max_fee_per_gas = 10;
    static constexpr uint256_t expected_priority_fee =
        gas_limit * max_fee_per_gas;
    Transaction const tx{
        .sc = {.r = 1, .s = 2, .y_parity = 0},
        .nonce = 0,
        .max_fee_per_gas = max_fee_per_gas,
        .gas_limit = gas_limit,
        .to = recipient,
    };

    BlockHeader const header{.beneficiary = beneficiary};
    BlockHashBufferFinalized const block_hash_buffer;

    boost::fibers::promise<void> prev{};
    prev.set_value();

    NoopCallTracer call_tracer;
    trace::StateTracer state_tracer = std::monostate{};
    auto const chain_ctx = ChainContext<Trait>::debug_empty();

    MonadDevnet const chain;
    auto const receipt = ExecuteTransaction<Trait>(
        chain,
        0, /* txn index */
        tx,
        from,
        {},
        header,
        block_hash_buffer,
        bs,
        metrics,
        prev,
        call_tracer,
        state_tracer,
        chain_ctx)();

    ASSERT_FALSE(receipt.has_error());
    EXPECT_EQ(receipt.value().status, 1u);

    State state{bs, Incarnation{0, 0}};
    if constexpr (Trait::mip_11_active()) {
        EXPECT_EQ(state.get_balance(beneficiary), 0);
        EXPECT_EQ(
            state.get_balance(staking::PRIORITY_FEE_DIST_ADDRESS),
            expected_priority_fee);
    }
    else {
        EXPECT_EQ(state.get_balance(beneficiary), expected_priority_fee);
        EXPECT_EQ(state.get_balance(staking::PRIORITY_FEE_DIST_ADDRESS), 0);
    }
}
