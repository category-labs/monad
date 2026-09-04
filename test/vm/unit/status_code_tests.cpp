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

#include <set>
#include <string_view>
#include <utility>
#include <vector>

namespace
{
    // evmc_status_code is two contiguous ranges. Sweeping them rather than a
    // list of names keeps these tests total over the enum; if evmc gains a code
    // outside them, -Wswitch in from_evmc_status_code fails first.
    constexpr int status_min = -3;
    constexpr int status_max = 18;

    std::vector<monad_status_code> all_status_codes()
    {
        std::vector<monad_status_code> codes;
        for (int i = status_min; i <= status_max; ++i) {
            codes.push_back(
                from_evmc_status_code(static_cast<evmc_status_code>(i)));
        }
        return codes;
    }
}

TEST(StatusCode, MirrorsEvmcValues)
{
    for (int i = status_min; i <= status_max; ++i) {
        auto const evmc_code = static_cast<evmc_status_code>(i);
        EXPECT_EQ(std::to_underlying(from_evmc_status_code(evmc_code)), i);
    }
}

TEST(StatusCode, RoundTripsThroughEvmc)
{
    for (auto const code : all_status_codes()) {
        EXPECT_EQ(
            std::to_underlying(
                from_evmc_status_code(to_evmc_status_code(code))),
            std::to_underlying(code));
    }
}

TEST(StatusCode, RoundTripsFromEvmc)
{
    for (int i = status_min; i <= status_max; ++i) {
        auto const evmc_code = static_cast<evmc_status_code>(i);
        EXPECT_EQ(
            std::to_underlying(
                to_evmc_status_code(from_evmc_status_code(evmc_code))),
            std::to_underlying(evmc_code));
    }
}

// -Wswitch gives us a case per code; only a test checks the string is right.
TEST(StatusCode, ToStringIsTotalAndDistinct)
{
    auto const codes = all_status_codes();
    std::set<std::string_view> seen;
    for (auto const code : codes) {
        std::string_view const name = monad_status_code_to_string(code);
        EXPECT_FALSE(name.empty())
            << "no string for status code " << std::to_underlying(code);
        EXPECT_TRUE(name.starts_with("MONAD_STATUS_"))
            << "unexpected spelling: " << name;
        EXPECT_TRUE(seen.insert(name).second) << "duplicate string: " << name;
    }
    EXPECT_EQ(seen.size(), codes.size());
}

TEST(StatusCode, ToStringNamesTheEnumerator)
{
    EXPECT_STREQ(
        monad_status_code_to_string(MONAD_STATUS_SUCCESS),
        "MONAD_STATUS_SUCCESS");
    EXPECT_STREQ(
        monad_status_code_to_string(MONAD_STATUS_OUT_OF_GAS),
        "MONAD_STATUS_OUT_OF_GAS");
    EXPECT_STREQ(
        monad_status_code_to_string(MONAD_STATUS_INTERNAL_ERROR),
        "MONAD_STATUS_INTERNAL_ERROR");
}

TEST(StatusCode, PreservesNegativeCodes)
{
    EXPECT_EQ(std::to_underlying(MONAD_STATUS_INTERNAL_ERROR), -1);
    EXPECT_EQ(std::to_underlying(MONAD_STATUS_REJECTED), -2);
    EXPECT_EQ(std::to_underlying(MONAD_STATUS_OUT_OF_MEMORY), -3);

    for (auto const code :
         {MONAD_STATUS_INTERNAL_ERROR,
          MONAD_STATUS_REJECTED,
          MONAD_STATUS_OUT_OF_MEMORY}) {
        EXPECT_LT(std::to_underlying(to_evmc_status_code(code)), 0);
        EXPECT_EQ(
            std::to_underlying(
                from_evmc_status_code(to_evmc_status_code(code))),
            std::to_underlying(code));
    }
}

// Fork-only, so no upstream reference; most likely value to move on a rebase.
TEST(StatusCode, MirrorsForkOnlyReserveBalanceViolation)
{
    EXPECT_EQ(std::to_underlying(MONAD_STATUS_RESERVE_BALANCE_VIOLATION), 18);
    EXPECT_EQ(
        std::to_underlying(
            to_evmc_status_code(MONAD_STATUS_RESERVE_BALANCE_VIOLATION)),
        std::to_underlying(EVMC_MONAD_RESERVE_BALANCE_VIOLATION));
    EXPECT_EQ(
        std::to_underlying(
            from_evmc_status_code(EVMC_MONAD_RESERVE_BALANCE_VIOLATION)),
        std::to_underlying(MONAD_STATUS_RESERVE_BALANCE_VIOLATION));
    EXPECT_STREQ(
        monad_status_code_to_string(MONAD_STATUS_RESERVE_BALANCE_VIOLATION),
        "MONAD_STATUS_RESERVE_BALANCE_VIOLATION");
}
