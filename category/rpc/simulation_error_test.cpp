// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/result.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/rpc/simulation_error.hpp>

#include <gtest/gtest.h>

#include <evmc/evmc.h>

#include <array>
#include <string_view>

using namespace monad;

TEST(SimulationErrorTest, SimulationDomain)
{
    struct TestCase
    {
        SimulationError error;
        std::string_view message;
    };

    constexpr std::array test_cases{
        TestCase{SimulationError::InvalidInput, "invalid input"},
        TestCase{SimulationError::InvalidData, "invalid data"},
        TestCase{
            SimulationError::WithdrawalsNotSupported,
            "Withdrawals are not supported on Monad"},
        TestCase{
            SimulationError::BlockNumbersNotIncreasing,
            "block numbers must be strictly increasing"},
        TestCase{
            SimulationError::BlockTimestampsNotMonotonic,
            "block timestamps must be monotonically increasing"},
        TestCase{
            SimulationError::SimulationHeaderNotAfterBase,
            "simulation header number must be greater than the base header "
            "number"},
        TestCase{
            SimulationError::TransactionsContextUnavailable,
            "failed to recover the transactions context"},
        TestCase{
            SimulationError::InvalidBlockGap,
            "the block gap must be exactly 1 after filling in synthetic "
            "blocks"},
        TestCase{SimulationError::GasLimitExceeded, "gas limit exceeded"},
    };

    for (auto const &test_case : test_cases) {
        Result<void>::error_type const error =
            static_cast<SimulationError>(test_case.error);
        auto const info = simulation_error_info(error);

        EXPECT_EQ(info.status_code, EVMC_INTERNAL_ERROR);
        EXPECT_EQ(info.message, test_case.message);
    }
}

TEST(SimulationErrorTest, BlockDomain)
{
    Result<void>::error_type const error = BlockError::GasAboveLimit;

    auto const info = simulation_error_info(error);

    EXPECT_EQ(info.status_code, EVMC_REJECTED);
    EXPECT_EQ(info.message, "gas above limit");
}
