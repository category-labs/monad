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

#include <category/vm/evm/status_code.h>

#include <evmc/evmc.h>

#include <gtest/gtest.h>
// magic_enum probes [-128,127] with static_cast; evmc_status_code has no
// fixed underlying type, so GCC flags the out-of-range casts.
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wconversion"
#include <magic_enum/magic_enum.hpp>
#pragma GCC diagnostic pop

#include <utility>

namespace
{
    constexpr auto evmc_status_codes =
        magic_enum::enum_values<evmc_status_code>();
    constexpr auto monad_status_codes =
        magic_enum::enum_values<monad_status_code>();
}

TEST(StatusCode, MirrorsEvmcValues)
{
    for (auto const evmc_code : evmc_status_codes) {
        EXPECT_EQ(
            std::to_underlying(from_evmc_status_code(evmc_code)),
            std::to_underlying(evmc_code));
    }
}

TEST(StatusCode, RoundTripsThroughEvmc)
{
    for (auto const code : monad_status_codes) {
        EXPECT_EQ(
            std::to_underlying(
                from_evmc_status_code(to_evmc_status_code(code))),
            std::to_underlying(code));
    }
}
