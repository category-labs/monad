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

#include "fixture.hpp"

#include <category/vm/runtime/data.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <limits>

using namespace monad;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

constexpr auto addr = vm::runtime::uint256_t{678};
constexpr auto wei = vm::runtime::uint256_t{782374};

TEST_F(RuntimeTest, BalanceHomestead)
{
    constexpr auto rev = EVMC_HOMESTEAD;
    auto f = wrap(balance<rev>);
    set_balance(addr, wei);

    ctx_.gas_remaining = 0;
    ASSERT_EQ(f(addr), wei);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, BalanceCancunCold)
{
    constexpr auto rev = EVMC_CANCUN;
    auto f = wrap(balance<rev>);
    set_balance(addr, wei);

    ctx_.gas_remaining = 2500;
    ASSERT_EQ(f(addr), wei);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, BalanceCancunWarm)
{
    constexpr auto rev = EVMC_CANCUN;
    auto f = wrap(balance<rev>);
    set_balance(addr, wei);
    host_.access_account(address_from_uint256(addr));

    ctx_.gas_remaining = 0;
    ASSERT_EQ(f(addr), wei);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, CallDataLoadInBounds)
{
    auto load = wrap(calldataload);

    ASSERT_EQ(
        load(0),
        0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F_u256);

    ASSERT_EQ(
        load(3),
        0x030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F202122_u256);

    ASSERT_EQ(
        load(96),
        0x606162636465666768696A6B6C6D6E6F707172737475767778797A7B7C7D7E7F_u256);
}

TEST_F(RuntimeTest, CallDataLoadOutOfBounds)
{
    auto load = wrap(calldataload);

    ASSERT_EQ(call(calldataload, std::numeric_limits<std::int64_t>::max()), 0);

    ASSERT_EQ(load(256), 0);

    ASSERT_EQ(
        load(97),
        0x6162636465666768696A6B6C6D6E6F707172737475767778797A7B7C7D7E7F00_u256);

    ASSERT_EQ(
        load(109),
        0x6D6E6F707172737475767778797A7B7C7D7E7F00000000000000000000000000_u256);
}

TEST_F(RuntimeTest, CallDataSize)
{
    ASSERT_EQ(ctx_.env.input_data_size, 128);
}

TEST_F(RuntimeTest, CallDataCopyAll)
{
    auto copy = wrap(calldatacopy);

    ctx_.gas_remaining = 24;
    copy(0, 0, 128);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 128);
    for (auto i = 0u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], i);
    }
}

TEST_F(RuntimeTest, CallDataCopyPartial)
{
    auto copy = wrap(calldatacopy);

    ctx_.gas_remaining = 12;
    copy(67, 5, 23);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 96);

    for (auto i = 0u; i < 67; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }

    for (auto i = 67u; i < 90; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], i - 62);
    }

    for (auto i = 90u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }
}

TEST_F(RuntimeTest, CallDataCopyOutOfBounds)
{
    auto copy = wrap(calldatacopy);

    ctx_.gas_remaining = 51;
    copy(17, 0, 256);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 288);

    for (auto i = 0u; i < 17; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }

    for (auto i = 17u; i < 145; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], i - 17);
    }

    for (auto i = 145u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }
}

TEST_F(RuntimeTest, CodeCopyAll)
{
    auto copy = wrap(codecopy);

    ctx_.gas_remaining = 24;
    copy(0, 0, 128);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 128);
    for (auto i = 0u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 127 - i);
    }
}

TEST_F(RuntimeTest, CodeCopyPartial)
{
    auto copy = wrap(codecopy);

    ctx_.gas_remaining = 12;
    copy(47, 12, 23);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 96);

    for (auto i = 0u; i < 47; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }

    for (auto i = 47u; i < 70; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 162 - i);
    }

    for (auto i = 70u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }
}

TEST_F(RuntimeTest, CodeCopyOutOfBounds)
{
    auto copy = wrap(codecopy);

    ctx_.gas_remaining = 51;
    copy(25, 0, 256);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 288);

    for (auto i = 0u; i < 25; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }

    for (auto i = 25u; i < 153; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 152 - i);
    }

    for (auto i = 153u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }
}

TEST_F(RuntimeTest, ExtCodeCopyHomestead)
{
    constexpr auto rev = EVMC_HOMESTEAD;
    auto copy = wrap(extcodecopy<rev>);

    host_.accounts[address_from_uint256(addr)].code =
        evmc::bytes(code_.begin(), code_.end());

    ctx_.gas_remaining = 6;
    copy(addr, 0, 0, 32);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 32);

    for (auto i = 0u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 127 - i);
    }
}

TEST_F(RuntimeTest, ExtCodeCopyCancunOutOfBounds)
{
    constexpr auto rev = EVMC_CANCUN;
    auto copy = wrap(extcodecopy<rev>);

    host_.accounts[address_from_uint256(addr)].code =
        evmc::bytes(code_.begin(), code_.end());

    ctx_.gas_remaining = 2506;
    copy(addr, 0, 112, 32);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 32);

    for (auto i = 0u; i < 16; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 15 - i);
    }

    for (auto i = 16u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], 0);
    }
}

TEST_F(RuntimeTest, ExtCodeSize)
{
    constexpr auto rev = EVMC_CANCUN;
    auto size = wrap(extcodesize<rev>);

    host_.accounts[address_from_uint256(addr)].code =
        evmc::bytes(code_.begin(), code_.end());

    ctx_.gas_remaining = 2500;

    ASSERT_EQ(size(addr), 128);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, ExtCodeHash)
{
    constexpr auto rev = EVMC_CANCUN;
    auto hash = wrap(extcodehash<rev>);

    host_.accounts[address_from_uint256(addr)].codehash =
        bytes32_from_uint256(713682);

    ctx_.gas_remaining = 2500;

    ASSERT_EQ(hash(addr), 713682);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, ReturnDataSize)
{
    auto return_data = result_data();
    ctx_.env.return_data = return_data.data();
    ctx_.env.return_data_size = return_data.size();

    ctx_.gas_remaining = 0;

    ASSERT_EQ(ctx_.env.return_data_size, 128);
    ASSERT_EQ(ctx_.gas_remaining, 0);
}

TEST_F(RuntimeTest, ReturnDataCopyAll)
{
    auto copy = wrap(returndatacopy);

    auto return_data = result_data();
    ctx_.env.return_data = return_data.data();
    ctx_.env.return_data_size = return_data.size();
    ctx_.gas_remaining = 24;
    copy(0, 0, 128);

    ASSERT_EQ(ctx_.gas_remaining, 0);
    ASSERT_EQ(ctx_.memory.size, 128);
    for (auto i = 0u; i < ctx_.memory.size; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], i);
    }
}
