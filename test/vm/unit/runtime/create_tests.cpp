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

#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/create.hpp>
#include <category/vm/runtime/memory.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.h>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

constexpr vm::runtime::uint256_t prog = 0x63FFFFFFFF6000526004601CF3_u256;
constexpr evmc_address result_addr = {0x42};

TEST_F(RuntimeTest, CreateFrontier)
{
    using traits = EvmTraits<EVMC_FRONTIER>;
    call(mstore, 0, prog);
    ASSERT_EQ(ctx_.memory.data[31], 0xF3);

    ctx_.gas_remaining = 1000000;
    host_.call_result = create_result(result_addr, 900000, 10);

    auto do_create = wrap(create<traits>);

    vm::runtime::uint256_t const addr = do_create(0, 19, 13);

    ASSERT_EQ(addr, uint256_from_address(result_addr));

    ASSERT_EQ(ctx_.gas_remaining, 900000);
    ASSERT_EQ(ctx_.gas_refund, 10);
}

TEST_F(RuntimeTest, CreateShanghai)
{
    using traits = EvmTraits<EVMC_SHANGHAI>;
    call(mstore, 0, prog);
    ASSERT_EQ(ctx_.memory.data[31], 0xF3);

    ctx_.gas_remaining = 1000000;
    host_.call_result = create_result(result_addr, 900000, 10);

    auto do_create = wrap(create<traits>);

    vm::runtime::uint256_t const addr = do_create(0, 19, 13);

    ASSERT_EQ(addr, uint256_from_address(result_addr));

    ASSERT_EQ(ctx_.gas_remaining, 915624);
    ASSERT_EQ(ctx_.gas_refund, 10);
}

TEST_F(RuntimeTest, CreateTangerineWhistle)
{
    using traits = EvmTraits<EVMC_TANGERINE_WHISTLE>;
    call(mstore, 0, prog);
    ASSERT_EQ(ctx_.memory.data[31], 0xF3);

    ctx_.gas_remaining = 1000000;
    host_.call_result = create_result(result_addr, 900000, 10);

    auto do_create = wrap(create<traits>);

    vm::runtime::uint256_t const addr = do_create(0, 19, 13);

    ASSERT_EQ(addr, uint256_from_address(result_addr));

    ASSERT_EQ(ctx_.gas_remaining, 915625);
    ASSERT_EQ(ctx_.gas_refund, 10);
}

TEST_F(RuntimeTest, CreateFrontierSizeIsZero)
{
    using traits = EvmTraits<EVMC_FRONTIER>;

    ctx_.gas_remaining = 1000000;
    host_.call_result = create_result(result_addr, 900000);

    auto do_create = wrap(create<traits>);

    vm::runtime::uint256_t const addr = do_create(0, 0, 0);

    ASSERT_EQ(addr, uint256_from_address(result_addr));
    ASSERT_EQ(ctx_.gas_remaining, 900000);
}

TEST_F(RuntimeTest, CreateFrontierFailure)
{
    using traits = EvmTraits<EVMC_FRONTIER>;

    host_.call_result = failure_result(EVMC_OUT_OF_GAS);

    auto do_create = wrap(create<traits>);

    vm::runtime::uint256_t const addr = do_create(0, 0, 0);

    ASSERT_EQ(addr, 0);
}

TEST_F(RuntimeTest, Create2Constantinople)
{
    using traits = EvmTraits<EVMC_CONSTANTINOPLE>;
    call(mstore, 0, prog);
    ASSERT_EQ(ctx_.memory.data[31], 0xF3);

    ctx_.gas_remaining = 1000000;
    host_.call_result = create_result(result_addr, 900000, 10);

    auto do_create2 = wrap(create2<traits>);

    vm::runtime::uint256_t const addr = do_create2(0, 19, 13, 0x99);

    ASSERT_EQ(addr, uint256_from_address(result_addr));

    ASSERT_EQ(ctx_.gas_remaining, 915624);
    ASSERT_EQ(ctx_.gas_refund, 10);
}

TEST_F(RuntimeTest, CreateMaxCodeSize)
{
    using traits = MonadTraits<MONAD_FOUR>;
    constexpr std::size_t max_initcode_size =
        2 * 128 * 1024; // max initcode size at MONAD_FOUR

    ctx_.gas_remaining = 1000000;
    host_.call_result = create_result(result_addr, 900000, 10);

    auto const do_create = wrap(create<traits>);
    auto const addr = do_create(0, 0, max_initcode_size);
    ASSERT_EQ(addr, uint256_from_address(result_addr));
}

TEST_F(RuntimeTest, Create2MaxCodeSize)
{
    using traits = MonadTraits<MONAD_FOUR>;
    constexpr std::size_t max_initcode_size =
        2 * 128 * 1024; // max initcode size at MONAD_FOUR

    ctx_.gas_remaining = 1000000;
    host_.call_result = create_result(result_addr, 900000, 10);

    auto const do_create2 = wrap(create2<traits>);
    auto const addr = do_create2(0, 0, max_initcode_size, 0);
    ASSERT_EQ(addr, uint256_from_address(result_addr));
}
