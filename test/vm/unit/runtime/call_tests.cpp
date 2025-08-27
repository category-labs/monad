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

#include <category/vm/runtime/call.hpp>
#include <category/vm/runtime/keccak.hpp>
#include <category/vm/runtime/transmute.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;
using namespace intx;

TEST_F(RuntimeTest, CallBasic)
{
    using traits = EvmChain<EVMC_CANCUN>;
    auto do_call = wrap(monad::vm::runtime::call<traits>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);
    host_.access_account(address_from_uint256(0));

    auto res = do_call(10000, 0, 0, 0, 0, 0, 32);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 32);
    for (auto i = 0u; i < 32; ++i) {
        ASSERT_EQ(ctx_.memory.data[i], i);
    }
    ASSERT_EQ(ctx_.gas_remaining, 91997);
}

TEST_F(RuntimeTest, CallWithValueCold)
{
    using traits = EvmChain<EVMC_CANCUN>;
    auto do_call = wrap(monad::vm::runtime::call<traits>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 55500);
}

TEST_F(RuntimeTest, CallGasLimit)
{
    using traits = EvmChain<EVMC_CANCUN>;
    auto do_call = wrap(monad::vm::runtime::call<traits>);

    ctx_.gas_remaining = 66500;
    host_.call_result = success_result(2000);

    auto res =
        do_call(std::numeric_limits<std::int64_t>::max(), 0, 0, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 3000);
}

TEST_F(RuntimeTest, CallFailure)
{
    using traits = EvmChain<EVMC_CANCUN>;
    auto do_call = wrap(monad::vm::runtime::call<traits>);

    ctx_.gas_remaining = 100000;
    host_.call_result = failure_result();

    auto res = do_call(10000, 0, 0, 0, 0, 0, 0);
    ASSERT_EQ(res, 0);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 87500);
}

TEST_F(RuntimeTest, DelegateCallIstanbul)
{
    using traits = EvmChain<EVMC_ISTANBUL>;
    auto do_call = wrap(monad::vm::runtime::delegatecall<traits>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 0, 0, 0, 0);
    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 92000);
}

TEST_F(RuntimeTest, CallCodeHomestead)
{
    using traits = EvmChain<EVMC_HOMESTEAD>;
    auto do_call = wrap(monad::vm::runtime::callcode<traits>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 34, 120, 2, 3, 54);
    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 128);
    ASSERT_EQ(ctx_.gas_remaining, 82988);
}

TEST_F(RuntimeTest, StaticCallByzantium)
{
    using traits = EvmChain<EVMC_BYZANTIUM>;
    auto do_call = wrap(monad::vm::runtime::staticcall<traits>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 23, 238, 890, 67);
    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 960);
    ASSERT_EQ(ctx_.gas_remaining, 91909);
}

TEST_F(RuntimeTest, CallTooDeep)
{
    using traits = EvmChain<EVMC_CANCUN>;
    auto do_call = wrap(monad::vm::runtime::call<traits>);

    ctx_.env.depth = 1024;
    ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 0);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 65800);
}

TEST_F(RuntimeTest, DelegatedCallPrague)
{
    using traits = EvmChain<EVMC_PRAGUE>;

    auto const delegate_addr = address_from_uint256(0xBEEF);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    add_account_at(0xC0FFEE, coffee_code);

    std::vector<uint8_t> beef_code = {0x00};
    add_account_at(0xBEEF, beef_code);

    ASSERT_EQ(host_.recorded_account_accesses.size(), 0);

    auto do_call = wrap(monad::vm::runtime::call<traits>);
    ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xC0FFEE)), EVMC_ACCESS_WARM);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xBEEF)), EVMC_ACCESS_WARM);
    ASSERT_EQ(host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        host_.recorded_calls[0].flags & static_cast<uint32_t>(EVMC_DELEGATED),
        static_cast<uint32_t>(EVMC_DELEGATED));
}

TEST_F(RuntimeTest, DelegatedStaticCallPrague)
{
    using traits = EvmChain<EVMC_PRAGUE>;

    auto const delegate_addr = address_from_uint256(0xBEEF);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    add_account_at(0xC0FFEE, coffee_code);

    std::vector<uint8_t> beef_code = {0x00};
    add_account_at(0xBEEF, beef_code);

    ASSERT_EQ(host_.recorded_account_accesses.size(), 0);

    auto do_call = wrap(monad::vm::runtime::staticcall<traits>);
    ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xC0FFEE)), EVMC_ACCESS_WARM);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xBEEF)), EVMC_ACCESS_WARM);
    ASSERT_EQ(host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        host_.recorded_calls[0].flags & static_cast<uint32_t>(EVMC_DELEGATED),
        static_cast<uint32_t>(EVMC_DELEGATED));
}

TEST_F(RuntimeTest, DelegatedDelegateCallPrague)
{
    using traits = EvmChain<EVMC_PRAGUE>;

    auto const delegate_addr = address_from_uint256(0xBEEF);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    add_account_at(0xC0FFEE, coffee_code);

    std::vector<uint8_t> beef_code = {0x00};
    add_account_at(0xBEEF, beef_code);

    ASSERT_EQ(host_.recorded_account_accesses.size(), 0);

    auto do_call = wrap(monad::vm::runtime::delegatecall<traits>);
    ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xC0FFEE)), EVMC_ACCESS_WARM);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xBEEF)), EVMC_ACCESS_WARM);
    ASSERT_EQ(host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        host_.recorded_calls[0].flags & static_cast<uint32_t>(EVMC_DELEGATED),
        static_cast<uint32_t>(EVMC_DELEGATED));
}

TEST_F(RuntimeTest, DelegatedCallcodePrague)
{
    using traits = EvmChain<EVMC_PRAGUE>;

    auto const delegate_addr = address_from_uint256(0xBEEF);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    add_account_at(0xC0FFEE, coffee_code);

    std::vector<uint8_t> beef_code = {0x00};
    add_account_at(0xBEEF, beef_code);

    ASSERT_EQ(host_.recorded_account_accesses.size(), 0);

    auto do_call = wrap(monad::vm::runtime::callcode<traits>);
    ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xC0FFEE)), EVMC_ACCESS_WARM);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xBEEF)), EVMC_ACCESS_WARM);
    ASSERT_EQ(host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        host_.recorded_calls[0].flags & static_cast<uint32_t>(EVMC_DELEGATED),
        static_cast<uint32_t>(EVMC_DELEGATED));
}

TEST_F(RuntimeTest, DelegatedCallPraguePrecompile)
{
    using traits = EvmChain<EVMC_PRAGUE>;

    auto const delegate_addr = address_from_uint256(0x01);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    add_account_at(0xC0FFEE, coffee_code);

    ASSERT_EQ(host_.recorded_account_accesses.size(), 0);

    auto do_call = wrap(monad::vm::runtime::call<traits>);
    ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(
        host_.access_account(address_from_uint256(0xC0FFEE)), EVMC_ACCESS_WARM);
    ASSERT_EQ(host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        host_.recorded_calls[0].flags & static_cast<uint32_t>(EVMC_DELEGATED),
        static_cast<uint32_t>(EVMC_DELEGATED));
}

TEST_F(RuntimeTest, DelegatedCallPragueBadCode1)
{
    using traits = EvmChain<EVMC_PRAGUE>;

    std::array<uint8_t, 2> baad_addr{0xBA, 0xAD};
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(baad_addr);
    add_account_at(0xC0FFEE, coffee_code);

    auto do_call = wrap(monad::vm::runtime::call<traits>);
    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        host_.recorded_calls[0].flags & static_cast<uint32_t>(EVMC_DELEGATED),
        0);
}

TEST_F(RuntimeTest, DelegatedCallPragueBadCode2)
{
    using traits = EvmChain<EVMC_PRAGUE>;

    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    add_account_at(0xC0FFEE, coffee_code);

    auto do_call = wrap(monad::vm::runtime::call<traits>);
    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        host_.recorded_calls[0].flags & static_cast<uint32_t>(EVMC_DELEGATED),
        0);
}
