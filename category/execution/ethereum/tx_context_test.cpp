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

// GASPRICE is an execution INPUT, not economics.
//
// A chain that meters gas without pricing it still has to report what an
// ordinary one would, because a contract can read this and branch on it, and a
// branch taken differently moves the state root. Economics is what moves
// balances, and that is gated elsewhere.
//
// The distinction had been lost once: an L2 build reported max_fee_per_gas
// here, which differs from the effective price for essentially every EIP-1559
// transaction. This test exists so it cannot be lost again, and it asserts the
// same thing on both arms -- which is the whole point.

#include <category/core/address.hpp>
#include <category/core/int.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <cstdint>

using namespace monad;

namespace
{
    constexpr uint256_t BASE_FEE = 100;

    /// A 1559 transaction whose cap is well above the base fee, so the
    /// effective price and the cap are different numbers and the test can tell
    /// which one came back.
    Transaction tx_1559()
    {
        Transaction tx{
            .max_fee_per_gas = 1000,
            .gas_limit = 21000,
            .type = TransactionType::eip1559,
            .max_priority_fee_per_gas = 7};
        tx.sc.chain_id = 1;
        return tx;
    }

    BlockHeader header_with_base_fee()
    {
        BlockHeader h{};
        h.number = 2;
        h.gas_limit = 30'000'000;
        h.base_fee_per_gas = BASE_FEE;
        return h;
    }

    uint256_t reported(Transaction const &tx, BlockHeader const &h)
    {
        auto const ctx = get_tx_context<EvmTraits<MONAD_ETH_PARIS>>(
            tx,
            Address{},
            h,
            uint256_t{1},
            // A real schedule: the context computes a blob base fee whether or
            // not the chain has blobs, and a zero update fraction divides by
            // zero. MONAD_BLOB_SCHEDULE is zero-limits with a live fraction for
            // exactly that reason.
            MONAD_BLOB_SCHEDULE);
        return load_be<uint256_t>(ctx.tx_gas_price);
    }
}

TEST(TxContext, GasPriceIsTheEffectivePriceAndNotTheCap)
{
    auto const tx = tx_1559();
    auto const h = header_with_base_fee();

    auto const effective = gas_price<EvmTraits<MONAD_ETH_PARIS>>(tx, BASE_FEE);

    // base_fee + priority, not the cap: 107 against 1000 here.
    EXPECT_EQ(reported(tx, h), effective);
    EXPECT_NE(reported(tx, h), uint256_t{tx.max_fee_per_gas});
}

// The two must differ for the assertion above to mean anything. Pinned so that
// a future change making them equal turns this file into a tautology loudly
// rather than quietly.
TEST(TxContext, TheCapAndTheEffectivePriceAreDifferentHere)
{
    auto const tx = tx_1559();
    EXPECT_NE(
        gas_price<EvmTraits<MONAD_ETH_PARIS>>(tx, BASE_FEE),
        uint256_t{tx.max_fee_per_gas});
}

// A header with no base fee leaves gas_price on its pre-London branch, where
// the cap IS the price. Nothing to distinguish there, and nothing to get wrong.
TEST(TxContext, WithoutABaseFeeTheCapIsThePrice)
{
    auto const tx = tx_1559();
    BlockHeader h = header_with_base_fee();
    h.base_fee_per_gas.reset();

    EXPECT_EQ(reported(tx, h), gas_price<EvmTraits<MONAD_ETH_PARIS>>(tx, 0));
}
