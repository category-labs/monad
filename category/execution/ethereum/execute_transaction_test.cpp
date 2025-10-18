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

#include <category/core/int.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <memory>
#include <optional>

using namespace monad;

using db_t = TrieDb;

TYPED_TEST(EvmTraitsTest, irrevocable_gas_and_refund_new_contract)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    {
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 56'000'000'000'000'000);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    Transaction const tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
        .nonce = 25,
        .max_fee_per_gas = 10,
        .gas_limit = 55'000,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer;

    boost::fibers::promise<void> prev{};
    prev.set_value();

    NoopCallTracer noop_call_tracer;
    trace::StateTracer noop_state_tracer = std::monostate{};

    auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
        EthereumMainnet{},
        0,
        tx,
        from,
        {},
        header,
        block_hash_buffer,
        bs,
        metrics,
        prev,
        noop_call_tracer,
        noop_state_tracer)();

    ASSERT_TRUE(!receipt.has_error());

    EXPECT_EQ(receipt.value().status, 1u);
    {
        State state{bs, Incarnation{0, 0}};
        if constexpr (TestFixture::Trait::evm_rev() == EVMC_FRONTIER) {
            EXPECT_EQ(
                intx::be::load<uint256_t>(state.get_balance(from)),
                uint256_t{55'999'999'999'790'000});
        }
        else {
            EXPECT_EQ(
                intx::be::load<uint256_t>(state.get_balance(from)),
                uint256_t{55'999'999'999'470'000});
        }

        EXPECT_EQ(state.get_nonce(from), 26); // EVMC will inc for creation
    }
    // check if miner gets the right reward
    if constexpr (TestFixture::Trait::evm_rev() == EVMC_FRONTIER) {
        EXPECT_EQ(receipt.value().gas_used * 10u, uint256_t{210'000});
    }
    else {
        EXPECT_EQ(receipt.value().gas_used * 10u, uint256_t{530'000});
    }
}

TYPED_TEST(MonadTraitsTest, TopLevelCreate)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    {
        constexpr uint256_t WEI_PER_MON{1000000000000000000};
        State state{bs, Incarnation{0, 0}};
        state.add_to_balance(from, 20 * WEI_PER_MON);
        state.set_nonce(from, 25);
        bs.merge(state);
    }

    auto const data = byte_string(154'776, '\x60');

    Transaction const tx{
        .sc =
            {.r =
                 0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
             .s =
                 0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
        .nonce = 25,
        .max_fee_per_gas = 100'000'000'000,
        .gas_limit = 68'491'176,
        .value = 0,
        .to = std::nullopt,
        .data = data,
    };

    BlockHeader const header{.beneficiary = bene};
    BlockHashBufferFinalized const block_hash_buffer;

    NoopCallTracer noop_call_tracer;
    trace::StateTracer noop_state_tracer = std::monostate{};

    boost::fibers::promise<void> prev{};
    prev.set_value();

    auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
        MonadTestnet{},
        0,
        tx,
        from,
        {},
        header,
        block_hash_buffer,
        bs,
        metrics,
        prev,
        noop_call_tracer,
        noop_state_tracer)();

    if constexpr (TestFixture::REV >= MONAD_TWO) {
        ASSERT_TRUE(!receipt.has_error());
    }
    else {
        ASSERT_TRUE(receipt.has_error());
    }
}

TYPED_TEST(MonadTraitsTest, refunds_delete)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    static constexpr auto initial_balance = 56'000'000'000'000'000;
    static constexpr auto max_fee_per_gas = 100'000'000'000;
    static constexpr auto gas_limit_tx1 = 200'000;
    static constexpr auto gas_limit_tx2 = 50'000;

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    // Sets s[0] = 1 if passed any data, clears s[0] if data is empty.
    auto const contract_code =
        evmc::from_hex("0x3615600a5760015f55005b5f5f55").value();

    {
        State state{bs, Incarnation{0, 0}};

        state.add_to_balance(from, initial_balance);
        state.set_nonce(from, 25);

        state.create_contract(contract);
        state.set_code(contract, contract_code);

        bs.merge(state);
    }

    // 0 -> 0 -> Z
    {
        Transaction const set_tx{
            .sc =
                {.r =
                     0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                 .s =
                     0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
            .nonce = 25,
            .max_fee_per_gas = max_fee_per_gas,
            .gas_limit = gas_limit_tx1,
            .to = contract,
            .data = evmc::from_hex("0x01").value(),
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;
        trace::StateTracer noop_state_tracer = std::monostate{};

        auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
            MonadDevnet{},
            0,
            set_tx,
            from,
            {},
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};

            if constexpr (TestFixture::Trait::monad_rev() == MONAD_ZERO) {
                // MONAD_ZERO charged gas used rather than full gas_limit
                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{initial_balance - (43'139 * max_fee_per_gas)});
            }
            else {
                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{
                        initial_balance - (gas_limit_tx1 * max_fee_per_gas)});
            }
        }
    }

    // X -> X -> 0
    {
        Transaction const zero_tx{
            .sc =
                {.r =
                     0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                 .s =
                     0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
            .nonce = 26,
            .max_fee_per_gas = max_fee_per_gas,
            .gas_limit = gas_limit_tx2,
            .to = contract,
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;
        trace::StateTracer noop_state_tracer = std::monostate{};

        auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
            MonadDevnet{},
            0,
            zero_tx,
            from,
            {},
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_FIVE) {

                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{
                        initial_balance -
                        ((gas_limit_tx1 + gas_limit_tx2) * max_fee_per_gas) +
                        (120'000 * max_fee_per_gas)});
            }
            else if constexpr (TestFixture::Trait::monad_rev() >= MONAD_ONE) {
                // No storage refunds before MONAD_FIVE
                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{
                        initial_balance -
                        ((gas_limit_tx1 + gas_limit_tx2) * max_fee_per_gas)});
            }
            else {
                // MONAD_ZERO charged gas used rather than full gas_limit
                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{
                        initial_balance -
                        ((43'139 + 21'223) * max_fee_per_gas)});
            }
        }
    }
}

TYPED_TEST(MonadTraitsTest, refunds_delete_then_set)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    static constexpr auto initial_balance = 56'000'000'000'000'000;
    static constexpr auto max_fee_per_gas = 100'000'000'000;

    static constexpr auto slot = bytes32_t{};
    auto const initial_value = intx::be::store<bytes32_t>(uint256_t{1});

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    vm::VM vm;
    BlockState bs{tdb, vm};
    BlockMetrics metrics;

    // s[0] = 0; s[0] = 1
    auto const contract_code = evmc::from_hex("0x5f5f5560015f55").value();

    {
        State state{bs, Incarnation{0, 0}};

        state.add_to_balance(from, initial_balance);
        state.set_nonce(from, 25);

        state.create_contract(contract);
        state.set_code(contract, contract_code);
        state.set_storage(contract, slot, initial_value);

        bs.merge(state);
    }

    // X -> X -> 0 then X -> 0 -> X
    {
        static constexpr auto gas_limit_tx =
            32'109 + 2300; // actual gas used + low gas SSTORE stipend

        Transaction const set_tx{
            .sc =
                {.r =
                     0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                 .s =
                     0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
            .nonce = 25,
            .max_fee_per_gas = max_fee_per_gas,
            .gas_limit = gas_limit_tx,
            .to = contract,
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;
        trace::StateTracer noop_state_tracer = std::monostate{};

        auto const receipt = ExecuteTransaction<typename TestFixture::Trait>(
            MonadDevnet{},
            0,
            set_tx,
            from,
            {},
            header,
            block_hash_buffer,
            bs,
            metrics,
            prev,
            noop_call_tracer,
            noop_state_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_FIVE) {

                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{
                        initial_balance - (gas_limit_tx * max_fee_per_gas) +
                        (2800 * max_fee_per_gas)});
            }
            else if constexpr (TestFixture::Trait::monad_rev() >= MONAD_ONE) {
                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{
                        initial_balance - (gas_limit_tx * max_fee_per_gas)});
            }
            else {
                EXPECT_EQ(
                    intx::be::load<uint256_t>(state.get_balance(from)),
                    uint256_t{initial_balance - (23'309 * max_fee_per_gas)});
            }
        }
    }
}
