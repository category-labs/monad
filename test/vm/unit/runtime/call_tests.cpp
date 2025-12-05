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

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

TYPED_TEST(RuntimeTraitsTest, CallBasic)
{
    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);

    this->ctx_.gas_remaining = 100000;
    this->host_.call_result = TestFixture::success_result(2000);
    this->host_.access_account(address_from_uint256(0));

    auto res = do_call(10000, 0, 0, 0, 0, 0, 32);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.memory.size, 32);
    for (auto i = 0u; i < 32; ++i) {
        ASSERT_EQ(this->ctx_.memory.data[i], i);
    }
    if constexpr (TestFixture::Trait::evm_rev() <= EVMC_TANGERINE_WHISTLE) {
        ASSERT_EQ(this->ctx_.gas_remaining, 66997);
    }
    else {
        ASSERT_EQ(this->ctx_.gas_remaining, 91997);
    }
}

TYPED_TEST(RuntimeTraitsTest, CallWithValueCold)
{
    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);

    this->ctx_.gas_remaining = 100000;
    this->host_.call_result = TestFixture::success_result(2000);

    auto res = do_call(10000, 0, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.memory.size, 0);
    constexpr auto gas_remaining = [] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                return 48'000;
            }
        }
        if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
            return 58'000;
        }
        else {
            return 55'500;
        }
    }();
    ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
}

TYPED_TEST(RuntimeTraitsTest, CallGasLimit)
{
    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);

    this->ctx_.gas_remaining = 66500;
    this->host_.call_result = TestFixture::success_result(2000);

    auto res =
        do_call(std::numeric_limits<std::int64_t>::max(), 0, 0, 0, 0, 0, 0);

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_TANGERINE_WHISTLE) {
        ASSERT_EQ(res, 1);
        ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(this->ctx_.memory.size, 0);

        constexpr auto gas_remaining = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                    return 2882;
                }
            }
            if constexpr (
                TestFixture::Trait::evm_rev() == EVMC_TANGERINE_WHISTLE) {
                return 2648;
            }
            else if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
                return 3039;
            }
            else {
                return 3000;
            }
        }();

        ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
    }
    else {
        ASSERT_EQ(this->ctx_.result.status, StatusCode::OutOfGas);
        // because set_return_data is not reached in this branch due to the
        // early exit, ASAN complains about a memory leak, since the destructor
        // of Environment would normally run std::free on this data.
        std::free(
            const_cast<std::uint8_t *>(this->host_.call_result.output_data));
    }
}

TYPED_TEST(RuntimeTraitsTest, CallFailure)
{
    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);

    this->ctx_.gas_remaining = 100000;
    this->host_.call_result = TestFixture::failure_result();

    auto res = do_call(10000, 0, 0, 0, 0, 0, 0);
    ASSERT_EQ(res, 0);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.memory.size, 0);

    constexpr auto gas_remaining = [] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                return 80'000;
            }
        }
        if constexpr (TestFixture::Trait::evm_rev() <= EVMC_TANGERINE_WHISTLE) {
            return 65'000;
        }
        else if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
            return 90'000;
        }
        else {
            return 87'500;
        }
    }();
    ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
}

TYPED_TEST(RuntimeTraitsTest, DelegateCall)
{
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_BYZANTIUM) {
        auto do_call = TestFixture::wrap(
            monad::vm::runtime::delegatecall<typename TestFixture::Trait>);

        this->ctx_.gas_remaining = 100000;
        this->host_.call_result = TestFixture::success_result(2000);

        auto res = do_call(10000, 0, 0, 0, 0, 0);
        ASSERT_EQ(res, 1);
        ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(this->ctx_.memory.size, 0);
        constexpr auto gas_remaining = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                    return 82'000;
                }
            }
            if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
                return 92'000;
            }
            else {
                return 89'500;
            }
        }();
        ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
    }
}

TYPED_TEST(RuntimeTraitsTest, CallCode)
{
    auto do_call = TestFixture::wrap(
        monad::vm::runtime::callcode<typename TestFixture::Trait>);

    this->ctx_.gas_remaining = 100000;
    this->host_.call_result = TestFixture::success_result(2000);

    auto res = do_call(10000, 0, 34, 120, 2, 3, 54);
    ASSERT_EQ(res, 1);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.memory.size, 128);
    constexpr auto gas_remaining = [] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                return 72'988;
            }
        }
        if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
            return 82'988;
        }
        else {
            return 80'488;
        }
    }();
    ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
}

TYPED_TEST(RuntimeTraitsTest, StaticCall)
{
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_BYZANTIUM) {
        auto do_call = TestFixture::wrap(
            monad::vm::runtime::staticcall<typename TestFixture::Trait>);

        this->ctx_.gas_remaining = 100000;
        this->host_.call_result = TestFixture::success_result(2000);

        auto res = do_call(10000, 0, 23, 238, 890, 67);
        ASSERT_EQ(res, 1);
        ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
        ASSERT_EQ(this->ctx_.memory.size, 960);
        constexpr auto gas_remaining = [] {
            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                    return 81'909;
                }
            }
            if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
                return 91'909;
            }
            else {
                return 89'409;
            }
        }();
        ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
    }
}

TYPED_TEST(RuntimeTraitsTest, CallTooDeep)
{
    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);

    this->ctx_.env.depth = 1024;
    this->ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 0);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->ctx_.memory.size, 0);
    constexpr auto gas_remaining = [] {
        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                return 58'300;
            }
        }
        if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
            return 68'300;
        }
        else {
            return 65'800;
        }
    }();
    ASSERT_EQ(this->ctx_.gas_remaining, gas_remaining);
}

TYPED_TEST(RuntimeTraitsTest, DelegatedCall)
{
    auto const delegate_addr = address_from_uint256(0xBEEF);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    TestFixture::add_account_at(0xC0FFEE, coffee_code);

    std::vector<uint8_t> beef_code = {0x00};
    TestFixture::add_account_at(0xBEEF, beef_code);

    ASSERT_EQ(this->host_.recorded_account_accesses.size(), 0);

    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);
    this->ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(
        this->host_.access_account(address_from_uint256(0xC0FFEE)),
        EVMC_ACCESS_WARM);
    TestFixture::assert_delegated(delegate_addr);
}

TYPED_TEST(RuntimeTraitsTest, DelegatedStaticCall)
{
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_BYZANTIUM) {
        auto const delegate_addr = address_from_uint256(0xBEEF);
        std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
        coffee_code.append_range(delegate_addr.bytes);
        ASSERT_EQ(coffee_code.size(), 23);
        TestFixture::add_account_at(0xC0FFEE, coffee_code);

        std::vector<uint8_t> beef_code = {0x00};
        TestFixture::add_account_at(0xBEEF, beef_code);

        ASSERT_EQ(this->host_.recorded_account_accesses.size(), 0);

        auto do_call = TestFixture::wrap(
            monad::vm::runtime::staticcall<typename TestFixture::Trait>);
        this->ctx_.gas_remaining = 100000;

        auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0);

        ASSERT_EQ(res, 1);
        ASSERT_EQ(
            this->host_.access_account(address_from_uint256(0xC0FFEE)),
            EVMC_ACCESS_WARM);
        TestFixture::assert_delegated(delegate_addr);
    }
}

TYPED_TEST(RuntimeTraitsTest, DelegatedDelegateCall)
{
    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_BYZANTIUM) {
        auto const delegate_addr = address_from_uint256(0xBEEF);
        std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
        coffee_code.append_range(delegate_addr.bytes);
        ASSERT_EQ(coffee_code.size(), 23);
        TestFixture::add_account_at(0xC0FFEE, coffee_code);

        std::vector<uint8_t> beef_code = {0x00};
        TestFixture::add_account_at(0xBEEF, beef_code);

        ASSERT_EQ(this->host_.recorded_account_accesses.size(), 0);

        auto do_call = TestFixture::wrap(
            monad::vm::runtime::delegatecall<typename TestFixture::Trait>);
        this->ctx_.gas_remaining = 100000;

        auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0);

        ASSERT_EQ(res, 1);
        if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
            ASSERT_EQ(
                this->host_.access_account(address_from_uint256(0xC0FFEE)),
                EVMC_ACCESS_COLD);
        }
        else {
            ASSERT_EQ(
                this->host_.access_account(address_from_uint256(0xC0FFEE)),
                EVMC_ACCESS_WARM);
        }
        TestFixture::assert_delegated(delegate_addr);
    }
}

TYPED_TEST(RuntimeTraitsTest, DelegatedCallcode)
{
    auto const delegate_addr = address_from_uint256(0xBEEF);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    TestFixture::add_account_at(0xC0FFEE, coffee_code);

    std::vector<uint8_t> beef_code = {0x00};
    TestFixture::add_account_at(0xBEEF, beef_code);

    ASSERT_EQ(this->host_.recorded_account_accesses.size(), 0);

    auto do_call = TestFixture::wrap(
        monad::vm::runtime::callcode<typename TestFixture::Trait>);
    this->ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    if constexpr (TestFixture::Trait::evm_rev() <= EVMC_ISTANBUL) {
        ASSERT_EQ(
            this->host_.access_account(address_from_uint256(0xC0FFEE)),
            EVMC_ACCESS_COLD);
    }
    else {
        ASSERT_EQ(
            this->host_.access_account(address_from_uint256(0xC0FFEE)),
            EVMC_ACCESS_WARM);
    }
    TestFixture::assert_delegated(delegate_addr);
}

TYPED_TEST(RuntimeTraitsTest, DelegatedCallPrecompile)
{
    auto const delegate_addr = address_from_uint256(0x01);
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(delegate_addr.bytes);
    ASSERT_EQ(coffee_code.size(), 23);
    TestFixture::add_account_at(0xC0FFEE, coffee_code);

    ASSERT_EQ(this->host_.recorded_account_accesses.size(), 0);

    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);
    this->ctx_.gas_remaining = 100000;

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(
        this->host_.access_account(address_from_uint256(0xC0FFEE)),
        EVMC_ACCESS_WARM);
    ASSERT_EQ(this->host_.recorded_calls.size(), 1);

    if constexpr (TestFixture::Trait::evm_rev() >= EVMC_PRAGUE) {
        ASSERT_EQ(
            this->host_.recorded_calls[0].flags &
                static_cast<uint32_t>(EVMC_DELEGATED),
            static_cast<uint32_t>(EVMC_DELEGATED));
    }
    else {
        ASSERT_NE(
            this->host_.recorded_calls[0].flags &
                static_cast<uint32_t>(EVMC_DELEGATED),
            static_cast<uint32_t>(EVMC_DELEGATED));
    }
}

TYPED_TEST(RuntimeTraitsTest, DelegatedCallBadCode1)
{
    std::array<uint8_t, 2> baad_addr{0xBA, 0xAD};
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    coffee_code.append_range(baad_addr);
    TestFixture::add_account_at(0xC0FFEE, coffee_code);

    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);
    this->ctx_.gas_remaining = 100000;
    this->host_.call_result = TestFixture::success_result(2000);

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        this->host_.recorded_calls[0].flags &
            static_cast<uint32_t>(EVMC_DELEGATED),
        0);
}

TYPED_TEST(RuntimeTraitsTest, DelegatedCallBadCode2)
{
    std::vector<uint8_t> coffee_code = {0xef, 0x01, 0x00};
    TestFixture::add_account_at(0xC0FFEE, coffee_code);

    auto do_call = TestFixture::wrap(
        monad::vm::runtime::call<typename TestFixture::Trait>);
    this->ctx_.gas_remaining = 100000;
    this->host_.call_result = TestFixture::success_result(2000);

    auto res = do_call(10000, 0xC0FFEE, 1, 0, 0, 0, 0);

    ASSERT_EQ(res, 1);
    ASSERT_EQ(this->ctx_.result.status, StatusCode::Success);
    ASSERT_EQ(this->host_.recorded_calls.size(), 1);
    ASSERT_EQ(
        this->host_.recorded_calls[0].flags &
            static_cast<uint32_t>(EVMC_DELEGATED),
        0);
}
