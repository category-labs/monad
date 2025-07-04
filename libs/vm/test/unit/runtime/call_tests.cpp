#include "fixture.hpp"

#include <monad/vm/runtime/call.hpp>
#include <monad/vm/runtime/transmute.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;
using namespace intx;

TEST_F(RuntimeTest, CallBasic)
{
    constexpr auto rev = EVMC_CANCUN;
    auto do_call = wrap(monad::vm::runtime::call<rev>);

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
    constexpr auto rev = EVMC_CANCUN;
    auto do_call = wrap(monad::vm::runtime::call<rev>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 55500);
}

TEST_F(RuntimeTest, CallGasLimit)
{
    constexpr auto rev = EVMC_CANCUN;
    auto do_call = wrap(monad::vm::runtime::call<rev>);

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
    constexpr auto rev = EVMC_CANCUN;
    auto do_call = wrap(monad::vm::runtime::call<rev>);

    ctx_.gas_remaining = 100000;
    host_.call_result = failure_result();

    auto res = do_call(10000, 0, 0, 0, 0, 0, 0);
    ASSERT_EQ(res, 0);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 87500);
}

TEST_F(RuntimeTest, DelegateCallIstanbul)
{
    constexpr auto rev = EVMC_ISTANBUL;
    auto do_call = wrap(monad::vm::runtime::delegatecall<rev>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 0, 0, 0, 0);
    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 92000);
}

TEST_F(RuntimeTest, CallCodeHomestead)
{
    constexpr auto rev = EVMC_HOMESTEAD;
    auto do_call = wrap(monad::vm::runtime::callcode<rev>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 34, 120, 2, 3, 54);
    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 128);
    ASSERT_EQ(ctx_.gas_remaining, 82988);
}

TEST_F(RuntimeTest, StaticCallByzantium)
{
    constexpr auto rev = EVMC_BYZANTIUM;
    auto do_call = wrap(monad::vm::runtime::staticcall<rev>);

    ctx_.gas_remaining = 100000;
    host_.call_result = success_result(2000);

    auto res = do_call(10000, 0, 23, 238, 890, 67);
    ASSERT_EQ(res, 1);
    ASSERT_EQ(ctx_.memory.size, 960);
    ASSERT_EQ(ctx_.gas_remaining, 91909);
}

TEST_F(RuntimeTest, CallTooDeep)
{
    constexpr auto rev = EVMC_CANCUN;
    auto do_call = wrap(monad::vm::runtime::call<rev>);

    ctx_.env.depth = 1024;
    ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 0);
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.gas_remaining, 65800);
}
