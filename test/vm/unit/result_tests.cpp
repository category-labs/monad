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

#include <category/core/address.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/status_code.h>

#include <test/vm/utils/evmc_result.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <utility>

using namespace monad::vm;

namespace
{
    constexpr uint8_t data[] = {1, 2, 3};

    uint8_t *malloc_copy_of_data()
    {
        auto *const buf = static_cast<uint8_t *>(std::malloc(sizeof(data)));
        std::memcpy(buf, data, sizeof(data));
        return buf;
    }

    bool holds_data(Result const &r)
    {
        return r.output_size == sizeof(data) &&
               std::memcmp(r.output_data, data, sizeof(data)) == 0;
    }
}

TEST(Result, CopyingConstructorCopiesOutput)
{
    Result const r{MONAD_STATUS_SUCCESS, 5, 1, data, sizeof(data)};
    EXPECT_EQ(r.status_code, MONAD_STATUS_SUCCESS);
    EXPECT_EQ(r.gas_left, 5);
    EXPECT_EQ(r.gas_refund, 1);
    EXPECT_NE(r.output_data, data);
    EXPECT_TRUE(holds_data(r));
}

TEST(Result, EmptyOutputIsNull)
{
    Result const r{MONAD_STATUS_SUCCESS, 0, 0, data, 0};
    EXPECT_EQ(r.output_data, nullptr);
    EXPECT_EQ(r.output_size, 0u);
}

TEST(Result, AdoptingConstructorTakesOwnership)
{
    auto *const buf = malloc_copy_of_data();
    Result const r{RawResult{
        .status_code = MONAD_STATUS_REVERT,
        .gas_left = 7,
        .gas_refund = 0,
        .output_data = buf,
        .output_size = sizeof(data),
        .create_address = {}}};
    EXPECT_EQ(r.output_data, buf);
    EXPECT_TRUE(holds_data(r));
}

TEST(Result, MoveEmptiesSource)
{
    Result a{MONAD_STATUS_SUCCESS, 1, 0, data, sizeof(data)};
    auto const *const buf = a.output_data;
    Result const b{std::move(a)};
    EXPECT_EQ(b.output_data, buf);
    EXPECT_EQ(a.output_data, nullptr);
    EXPECT_EQ(a.output_size, 0u);
}

TEST(Result, MoveAssignReplacesOutput)
{
    Result a{MONAD_STATUS_SUCCESS, 1, 0, data, sizeof(data)};
    Result b{MONAD_STATUS_REVERT, 2, 0, data, sizeof(data)};
    auto const *const buf = b.output_data;
    a = std::move(b);
    EXPECT_EQ(a.status_code, MONAD_STATUS_REVERT);
    EXPECT_EQ(a.output_data, buf);
    EXPECT_EQ(b.output_data, nullptr);
}

TEST(Result, SelfMoveAssignKeepsOutput)
{
    Result a{MONAD_STATUS_SUCCESS, 1, 0, data, sizeof(data)};
    auto const *const buf = a.output_data;
    auto &alias = a;
    a = std::move(alias);
    EXPECT_EQ(a.output_data, buf);
    EXPECT_TRUE(holds_data(a));
}

TEST(Result, ReleaseRawGivesUpOwnership)
{
    Result r{MONAD_STATUS_SUCCESS, 3, 0, data, sizeof(data)};
    auto const raw = r.release_raw();
    EXPECT_EQ(r.output_data, nullptr);
    EXPECT_EQ(raw.gas_left, 3);
    ASSERT_EQ(raw.output_size, sizeof(data));
    EXPECT_EQ(std::memcmp(raw.output_data, data, sizeof(data)), 0);
    std::free(const_cast<uint8_t *>(raw.output_data));
}

TEST(Result, EvmcRoundTripKeepsFields)
{
    Result in{MONAD_STATUS_REVERT, 9, 0, data, sizeof(data)};
    in.create_address = monad::Address{0x42};
    auto const out =
        test::from_evmc_result(test::to_evmc_result(std::move(in)));
    EXPECT_EQ(out.status_code, MONAD_STATUS_REVERT);
    EXPECT_EQ(out.gas_left, 9);
    EXPECT_EQ(out.create_address, monad::Address{0x42});
    EXPECT_TRUE(holds_data(out));
}
