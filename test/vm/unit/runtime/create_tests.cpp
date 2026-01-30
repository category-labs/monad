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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/create.hpp>
#include <category/vm/runtime/memory.hpp>
#include <category/vm/runtime/transmute.hpp>

#include <evmc/evmc.h>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

constexpr vm::runtime::uint256_t prog = 0x63FFFFFFFF6000526004601CF3_u256;
constexpr evmc_address result_addr = {0x42};

TYPED_TEST(RuntimeTraitsTest, Create)
{
    TestFixture::call(mstore<typename TestFixture::Trait>, 0, prog);
    ASSERT_EQ(this->ctx_.memory.data[31], 0xF3);

    this->ctx_.gas_remaining = 1000000;
    this->host_.call_result =
        TestFixture::create_result(result_addr, 900000, 10);

    auto do_create = TestFixture::wrap(create<typename TestFixture::Trait>);

    vm::runtime::uint256_t const addr = do_create(0, 19, 13);

    ASSERT_EQ(addr, uint256_from_address(result_addr));
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    constexpr auto gas_remaining = [] {
        if constexpr (TestFixture::Trait::evm_rev() < EVMC_TANGERINE_WHISTLE) {
            return 900'000;
        }
        else if constexpr (TestFixture::Trait::evm_rev() < EVMC_SHANGHAI) {
            return 915'625;
        }
        else {
            return 915'624;
        }
    }();
    ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
    ASSERT_EQ(this->ctx_.gas_refund, 10);
}

TYPED_TEST(RuntimeTraitsTest, CreateSizeIsZero)
{
    this->ctx_.gas_remaining = 1000000;
    this->host_.call_result = TestFixture::create_result(result_addr, 900000);

    auto do_create = TestFixture::wrap(create<typename TestFixture::Trait>);

    vm::runtime::uint256_t const addr = do_create(0, 0, 0);

    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(addr, uint256_from_address(result_addr));
    constexpr auto gas_remaining = [] {
        if constexpr (TestFixture::Trait::evm_rev() < EVMC_TANGERINE_WHISTLE) {
            return 900'000;
        }
        else {
            return 915'625;
        }
    }();
    ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
}

TYPED_TEST(RuntimeTraitsTest, CreateFailure)
{
    this->host_.call_result = TestFixture::failure_result(EVMC_OUT_OF_GAS);

    auto do_create = TestFixture::wrap(create<typename TestFixture::Trait>);

    vm::runtime::uint256_t const addr = do_create(0, 0, 0);

    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(addr, 0);
}

TYPED_TEST(RuntimeTraitsTest, Create2)
{
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_CONSTANTINOPLE) {
        TestFixture::call(mstore<typename TestFixture::Trait>, 0, prog);
        ASSERT_EQ(this->ctx_.memory.data[31], 0xF3);

        this->ctx_.gas_remaining = 1000000;
        this->host_.call_result =
            TestFixture::create_result(result_addr, 900000, 10);

        auto do_create2 =
            TestFixture::wrap(create2<typename TestFixture::Trait>);

        vm::runtime::uint256_t const addr = do_create2(0, 19, 13, 0x99);

        ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(addr, uint256_from_address(result_addr));

        ASSERT_EQ(this->ctx_.gas_remaining, 915624);
        ASSERT_EQ(this->ctx_.gas_refund, 10);
    }
}

TYPED_TEST(RuntimeTraitsTest, CreateAtMaxCodeSize)
{

    constexpr std::size_t max_initcode_size = [] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_FOUR) {
                return 2 * 128 * 1024;
            }
        }
        return 2 * 24 * 1024; // max initcode size since EIP-3860
    }();

    this->ctx_.gas_remaining = 1000000;
    this->host_.call_result =
        TestFixture::create_result(result_addr, 900000, 10);

    auto const do_create =
        TestFixture::wrap(create<typename TestFixture::Trait>);
    auto const addr = do_create(0, 0, max_initcode_size);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(addr, uint256_from_address(result_addr));
}

TYPED_TEST(RuntimeTraitsTest, CreateAboveMaxCodeSize)
{
    // init code size was unbounded before Shanghai
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_SHANGHAI) {

        constexpr std::size_t max_initcode_size = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() >= MONAD_FOUR) {
                    return 2 * 128 * 1024;
                }
            }
            return 2 * 24 * 1024; // max initcode size since EIP-3860
        }();

        this->ctx_.gas_remaining = 1000000;
        this->host_.call_result =
            TestFixture::create_result(result_addr, 900000, 10);

        auto const do_create =
            TestFixture::wrap(create<typename TestFixture::Trait>);
        auto const addr = do_create(0, 0, max_initcode_size + 1);
        ASSERT_EQ(this->ctx_.result.status, StatusCode::OutOfGas);
        ASSERT_EQ(addr, 0);

        std::free(
            const_cast<std::uint8_t *>(this->host_.call_result.output_data));
    }
}

TYPED_TEST(RuntimeTraitsTest, Create2AtMaxCodeSize)
{
    constexpr std::size_t max_initcode_size = [] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_FOUR) {
                return 2 * 128 * 1024;
            }
        }
        return 2 * 24 * 1024; // max initcode size since EIP-3860
    }();
    this->ctx_.gas_remaining = 1000000;
    this->host_.call_result =
        TestFixture::create_result(result_addr, 900000, 10);

    auto const do_create2 =
        TestFixture::wrap(create2<typename TestFixture::Trait>);
    auto const addr = do_create2(0, 0, max_initcode_size, 0);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(addr, uint256_from_address(result_addr));
}

TYPED_TEST(RuntimeTraitsTest, Create2AboveMaxCodeSize)
{
    // init code size was unbounded before Shanghai
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_SHANGHAI) {

        constexpr std::size_t max_initcode_size = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() >= MONAD_FOUR) {
                    return 2 * 128 * 1024;
                }
            }
            return 2 * 24 * 1024; // max initcode size since EIP-3860
        }();

        this->ctx_.gas_remaining = 1000000;
        this->host_.call_result =
            TestFixture::create_result(result_addr, 900000, 10);

        auto const do_create2 =
            TestFixture::wrap(create2<typename TestFixture::Trait>);
        auto const addr = do_create2(0, 0, max_initcode_size + 1, 0);
        ASSERT_EQ(this->ctx_.result.status, StatusCode::OutOfGas);
        ASSERT_EQ(addr, 0);

        std::free(
            const_cast<std::uint8_t *>(this->host_.call_result.output_data));
    }
}
