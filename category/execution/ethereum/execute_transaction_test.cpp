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
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>

#include <gtest/gtest.h>

#include <memory>
#include <optional>

using namespace monad;

using db_t = TrieDb;

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
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

    auto const receipt = ExecuteTransaction<EvmTraits<EVMC_SHANGHAI>>(
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
        noop_call_tracer)();

    ASSERT_TRUE(!receipt.has_error());

    EXPECT_EQ(receipt.value().status, 1u);
    {
        State state{bs, Incarnation{0, 0}};
        EXPECT_EQ(
            intx::be::load<uint256_t>(state.get_balance(from)),
            uint256_t{55'999'999'999'470'000});
        EXPECT_EQ(state.get_nonce(from), 26); // EVMC will inc for creation
    }

    // check if miner gets the right reward
    EXPECT_EQ(receipt.value().gas_used * 10u, uint256_t{530'000});
}

TEST(TransactionProcessor, monad_five_refunds_delete)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

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

        state.add_to_balance(from, 56'000'000'000'000'000);
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
            .max_fee_per_gas = 100'000'000'000,
            .gas_limit = 151'039,
            .to = contract,
            .data = evmc::from_hex("0x01").value(),
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;

        auto const receipt = ExecuteTransaction<MonadTraits<MONAD_FIVE>>(
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
            noop_call_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            EXPECT_EQ(
                intx::be::load<uint256_t>(state.get_balance(from)),
                uint256_t{40'896'100'000'000'000});
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
            .max_fee_per_gas = 100'000'000'000,
            .gas_limit = 26'023,
            .to = contract,
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;

        auto const receipt = ExecuteTransaction<MonadTraits<MONAD_FIVE>>(
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
            noop_call_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            EXPECT_EQ(
                intx::be::load<uint256_t>(state.get_balance(from)),
                uint256_t{
                    38'293'800'000'000'000 + (120'000 * 100'000'000'000)});
        }
    }
}

TEST(TransactionProcessor, monad_five_refunds_delete_then_set)
{
    using intx::operator""_u256;

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto contract{
        0x00000000000000000000000000000000cccccccc_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

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

        state.add_to_balance(from, 56'000'000'000'000'000);
        state.set_nonce(from, 25);

        state.create_contract(contract);
        state.set_code(contract, contract_code);
        state.set_storage(contract, slot, initial_value);

        bs.merge(state);
    }

    // X -> X -> 0 then X -> 0 -> X
    {
        Transaction const set_tx{
            .sc =
                {.r =
                     0x5fd883bb01a10915ebc06621b925bd6d624cb6768976b73c0d468b31f657d15b_u256,
                 .s =
                     0x121d855c539a23aadf6f06ac21165db1ad5efd261842e82a719c9863ca4ac04c_u256},
            .nonce = 25,
            .max_fee_per_gas = 100'000'000'000,
            .gas_limit =
                26'109 + 2300, // actual gas used + low gas SSTORE stipend
            .to = contract,
        };

        BlockHeader const header{.beneficiary = bene};
        BlockHashBufferFinalized const block_hash_buffer;

        boost::fibers::promise<void> prev{};
        prev.set_value();

        NoopCallTracer noop_call_tracer;

        auto const receipt = ExecuteTransaction<MonadTraits<MONAD_FIVE>>(
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
            noop_call_tracer)();

        ASSERT_TRUE(!receipt.has_error());
        EXPECT_EQ(receipt.value().status, 1u);

        {
            State state{bs, Incarnation{0, 0}};
            EXPECT_EQ(
                intx::be::load<uint256_t>(state.get_balance(from)),
                uint256_t{53'159'100'000'000'000 + (2800 * 100'000'000'000)});
        }
    }
}
