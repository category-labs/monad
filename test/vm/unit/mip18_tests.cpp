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

#include "evm_fixture.hpp"

#include <category/core/address.hpp>
#include <category/core/int.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/runtime/transmute.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::vm::compiler;
using namespace monad::vm::test;

namespace
{
    constexpr std::array<Address, 4> senders{
        0x00000000000000000000000000000000000000a0_address,
        0x00000000000000000000000000000000000000a1_address,
        0x00000000000000000000000000000000000000a2_address,
        0x00000000000000000000000000000000000000a3_address,
    };

    std::vector<uint8_t> return_top(std::vector<uint8_t> code)
    {
        code.insert(code.end(), {PUSH0, MSTORE, PUSH1, 32, PUSH0, RETURN});
        return code;
    }
}

TYPED_TEST(VMTraitsTest, CallStackDepth)
{
    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    this->msg_.depth = 5;
    auto const code = return_top({EXTENSION, CALLSTACKDEPTH});

    for (auto const impl : impls) {
        TestFixture::execute(100'000, code, {}, impl);
        if constexpr (TestFixture::Trait::mip_18_active()) {
            ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
            ASSERT_EQ(
                load_be_unsafe<uint256_t>(this->result_.output_data),
                uint256_t{5});
        }
        else {
            ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
            ASSERT_EQ(this->result_.gas_left, 0);
        }
    }
}

TYPED_TEST(VMTraitsTest, CallerN)
{
    if constexpr (!TestFixture::Trait::mip_18_active()) {
        GTEST_SKIP() << "MIP-18 is not active";
    }

    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    this->msg_.depth = 3;
    this->msg_.sender = senders[3];
    for (size_t i = 0; i < senders.size(); ++i) {
        this->host_.set_call_frame_sender(i, senders[i]);
    }

    auto const callern = [](std::vector<uint8_t> push_n) {
        push_n.insert(push_n.end(), {EXTENSION, CALLERN});
        return return_top(std::move(push_n));
    };

    std::vector<uint8_t> push_max{PUSH32};
    std::fill_n(std::back_inserter(push_max), 32, 0xff);

    std::vector<std::pair<std::vector<uint8_t>, uint256_t>> const cases{
        {{PUSH0}, vm::runtime::uint256_from_address(senders[3])},
        {{PUSH1, 1}, vm::runtime::uint256_from_address(senders[2])},
        {{PUSH1, 2}, vm::runtime::uint256_from_address(senders[1])},
        {{PUSH1, 3}, vm::runtime::uint256_from_address(senders[0])},
        {{PUSH1, 4}, 0},
        {{PUSH9, 1, 0, 0, 0, 0, 0, 0, 0, 0}, 0},
        {push_max, 0},
    };

    for (auto const impl : impls) {
        for (auto const &[push_n, expected] : cases) {
            TestFixture::execute(100'000, callern(push_n), {}, impl);
            ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
            ASSERT_EQ(
                load_be_unsafe<uint256_t>(this->result_.output_data), expected);
        }
    }
}

TYPED_TEST(VMTraitsTest, CallStackMaxDepth)
{
    if constexpr (!TestFixture::Trait::mip_18_active()) {
        GTEST_SKIP() << "MIP-18 is not active";
    }

    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    this->msg_.depth = 1024;
    this->host_.set_call_frame_sender(0, senders[0]);
    this->host_.set_call_frame_sender(1024, senders[3]);

    for (auto const impl : impls) {
        TestFixture::execute(
            100'000, return_top({EXTENSION, CALLSTACKDEPTH}), {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(
            load_be_unsafe<uint256_t>(this->result_.output_data),
            uint256_t{1024});

        TestFixture::execute(
            100'000,
            return_top({PUSH2, 0x04, 0x00, EXTENSION, CALLERN}),
            {},
            impl);
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(
            load_be_unsafe<uint256_t>(this->result_.output_data),
            vm::runtime::uint256_from_address(senders[0]));
    }
}

TYPED_TEST(VMTraitsTest, ExtensionGas)
{
    if constexpr (!TestFixture::Trait::mip_18_active()) {
        GTEST_SKIP() << "MIP-18 is not active";
    }

    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    this->host_.set_call_frame_sender(0, this->msg_.sender);

    for (auto const impl : impls) {
        TestFixture::execute(2, {EXTENSION, CALLSTACKDEPTH}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(this->result_.gas_left, 0);

        TestFixture::execute(1, {EXTENSION, CALLSTACKDEPTH}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_OUT_OF_GAS);
        ASSERT_EQ(this->result_.gas_left, 0);

        TestFixture::execute(4, {PUSH0, EXTENSION, CALLERN}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        ASSERT_EQ(this->result_.gas_left, 0);

        TestFixture::execute(3, {PUSH0, EXTENSION, CALLERN}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_OUT_OF_GAS);
        ASSERT_EQ(this->result_.gas_left, 0);
    }
}

TYPED_TEST(VMTraitsTest, ExtensionStackLimits)
{
    if constexpr (!TestFixture::Trait::mip_18_active()) {
        GTEST_SKIP() << "MIP-18 is not active";
    }

    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    this->host_.set_call_frame_sender(0, this->msg_.sender);

    std::vector<uint8_t> full_stack(1024, GAS);

    auto overflow = full_stack;
    overflow.insert(overflow.end(), {EXTENSION, CALLSTACKDEPTH});

    auto callern_on_full_stack = full_stack;
    callern_on_full_stack.insert(
        callern_on_full_stack.end(), {EXTENSION, CALLERN});

    for (auto const impl : impls) {
        TestFixture::execute(100'000, {EXTENSION, CALLERN}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
    }

    TestFixture::execute(
        100'000, overflow, {}, TestFixture::Implementation::Interpreter);
    ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);

    TestFixture::execute(
        100'000,
        callern_on_full_stack,
        {},
        TestFixture::Implementation::Interpreter);
    ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
}

TYPED_TEST(VMTraitsTest, ExtensionInvalidSelector)
{
    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    for (uint8_t const selector :
         std::array<uint8_t, 5>{0x02, 0x5B, 0x60, 0x7F, 0xFF}) {
        for (auto const impl : impls) {
            TestFixture::execute(100'000, {EXTENSION, selector}, {}, impl);
            ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
            ASSERT_EQ(this->result_.gas_left, 0);
        }
    }
}

TYPED_TEST(VMTraitsTest, ExtensionJumpdestAnalysis)
{
    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    for (auto const impl : impls) {
        TestFixture::execute(
            100'000, {PUSH1, 4, JUMP, EXTENSION, JUMPDEST, STOP}, {}, impl);
        ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);

        TestFixture::execute(
            100'000,
            {PUSH1, 5, JUMP, EXTENSION, PUSH1, JUMPDEST, STOP},
            {},
            impl);
        ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
    }
}

TYPED_TEST(VMTraitsTest, ExtensionAtEndOfCode)
{
    auto const impls = {
        TestFixture::Implementation::Compiler,
        TestFixture::Implementation::Interpreter};

    for (auto const impl : impls) {
        TestFixture::execute(2, {EXTENSION}, {}, impl);
        if constexpr (TestFixture::Trait::mip_18_active()) {
            ASSERT_EQ(this->result_.status_code, EVMC_SUCCESS);
        }
        else {
            ASSERT_EQ(this->result_.status_code, EVMC_FAILURE);
        }
        ASSERT_EQ(this->result_.gas_left, 0);
    }
}
