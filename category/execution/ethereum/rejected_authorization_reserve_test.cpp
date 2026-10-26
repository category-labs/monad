// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/core/fiber/priority_pool.hpp>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/units.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/vm/vm.hpp>

#include <boost/fiber/future/future.hpp>
#include <boost/fiber/future/promise.hpp>
#include <gtest/gtest.h>

#include <array>
#include <memory>
#include <optional>
#include <variant>
#include <vector>

using namespace monad;

template <typename Traits>
class RejectedAuthorizationReserveTest : public ::testing::Test
{
};

using Revisions =
    ::testing::Types<MonadTraits<MONAD_EIGHT>, MonadTraits<MONAD_NINE>>;
TYPED_TEST_SUITE(RejectedAuthorizationReserveTest, Revisions);

TYPED_TEST(
    RejectedAuthorizationReserveTest, rejected_authority_prevents_emptying)
{
    constexpr auto alice = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address;
    constexpr auto recipient = Address{0x2000};
    constexpr auto initial_balance = uint256_t{10} * ETHER;
    constexpr auto gas_limit = 200'000;

    // Same signed transaction as monad-execution-specs issue #72's OCaml test:
    // chain 1, nonce 0, gas price 1, value 1 wei, self-authorization nonce 0,
    // delegate 0x3000. Both signatures use the standard test private key
    // 45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8.
    auto const encoded =
        from_hex("04f8c10180010183030d40940000000000000000000000000000000000002"
                 "0000180c0f85cf85a01940000000000000000"
                 "0000000000000000000030008080a085fd3f8aaa96b30ca6948aa2ad02b8b"
                 "360f733cddad2fc791b9debeddb66e1a5a077"
                 "4116115f9a9e4cfe242480146e744dcb739cf0d1dcb8bb03cac9942aa0cda"
                 "101a0264d31e45b11e09c53ef76e605b4aa99"
                 "458321861ff358bca2a6fafadce1ab24a063e37432a701ed3dcbff1218528"
                 "59d1b463b07b00a9fbb6dc78a652af399e8a0")
            .value();
    byte_string_view encoded_view{encoded};
    auto const decoded = rlp::decode_transaction(encoded_view);
    ASSERT_FALSE(decoded.has_error());
    ASSERT_TRUE(encoded_view.empty());
    auto const &tx = decoded.value();
    ASSERT_EQ(recover_sender(tx), alice);
    ASSERT_EQ(tx.nonce, 0);
    ASSERT_EQ(tx.gas_limit, gas_limit);
    ASSERT_EQ(tx.value, 1);
    ASSERT_EQ(tx.to, recipient);
    ASSERT_EQ(tx.authorization_list.size(), 1);
    ASSERT_EQ(tx.authorization_list.front().nonce, 0);

    fiber::PriorityPool pool{1, 1};
    std::array<Transaction, 1> const transactions{tx};
    auto const authorities = recover_authorities(transactions, pool);
    ASSERT_EQ(authorities.at(0).at(0), alice);
    std::vector<Address> const senders{alice};
    auto const senders_and_authorities =
        combine_senders_and_authorities(senders, authorities);
    ankerl::unordered_dense::segmented_set<Address> const no_prior_activity{};
    ChainContext<TypeParam> const ctx{
        no_prior_activity,
        no_prior_activity,
        senders_and_authorities,
        senders,
        authorities};

    mpt::Db db{std::make_unique<InMemoryMachine>()};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    {
        State initial{bs, Incarnation{0, 0}};
        initial.add_to_balance(alice, initial_balance);
        bs.merge(initial);
    }
    BlockHeader const header{
        .number = 10, .gas_limit = 1'000'000, .base_fee_per_gas = 0};
    BlockHashBufferFinalized const block_hash_buffer;
    BlockMetrics metrics;
    boost::fibers::promise<void> previous;
    auto ready = previous.get_future();
    previous.set_value();
    NoopCallTracer call_tracer;
    trace::StateTracer state_tracer = std::monostate{};
    auto const receipt = ExecuteTransaction<TypeParam>{
        EthereumMainnet{},
        0,
        tx,
        alice,
        authorities.at(0),
        header,
        block_hash_buffer,
        bs,
        metrics,
        ready,
        call_tracer,
        state_tracer,
        ctx,
        nullptr}();
    ASSERT_FALSE(receipt.has_error());

    // Application rejects nonce 0 after the sender nonce becomes 1, but the
    // recovered authority still forbids emptying. The reserve check rolls
    // back the transfer without rolling back the fee or transaction nonce.
    EXPECT_EQ(receipt.value().status, 0);
    EXPECT_EQ(receipt.value().gas_used, gas_limit);
    State after{bs, Incarnation{10, 1}};
    EXPECT_EQ(after.get_balance(recipient), 0);
    EXPECT_EQ(after.get_balance(alice), initial_balance - gas_limit);
    EXPECT_EQ(after.get_nonce(alice), 1);
    EXPECT_EQ(after.get_code_hash(alice), NULL_HASH);
}
