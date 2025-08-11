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

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86/virtual_stack.hpp>
#include <category/vm/evm/opcodes.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <set>
#include <utility>
#include <vector>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::native;

namespace
{
    struct StackElemTestData
    {
        explicit StackElemTestData(std::set<std::int32_t> stack_indices)
            : stack_indices{std::move(stack_indices)}
        {
        }

        StackElemTestData &with_stack_offset(StackOffset x)
        {
            stack_offset = x;
            return *this;
        }

        StackElemTestData &with_avx_reg(AvxReg x)
        {
            avx_reg = x;
            return *this;
        }

        StackElemTestData &with_general_reg(GeneralReg x)
        {
            general_reg = x;
            return *this;
        }

        StackElemTestData &with_literal(Literal x)
        {
            literal = x;
            return *this;
        }

        std::optional<StackOffset> stack_offset;
        std::optional<AvxReg> avx_reg;
        std::optional<GeneralReg> general_reg;
        std::optional<Literal> literal;
        std::set<std::int32_t> stack_indices;
    };

    bool test_stack_element(StackElemRef e, StackElemTestData t)
    {
        return e->stack_offset() == t.stack_offset &&
               e->avx_reg() == t.avx_reg && e->general_reg() == t.general_reg &&
               e->literal() == t.literal &&
               e->stack_indices() == t.stack_indices;
    }
}

TEST(VirtualStack, ctor_test_1)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({ADD});
    Stack stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -2);
    ASSERT_EQ(stack.max_delta(), 0);
    ASSERT_EQ(stack.delta(), -1);
    ASSERT_TRUE(test_stack_element(
        stack.get(-2), StackElemTestData{{-2}}.with_stack_offset({-2})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1}}.with_stack_offset({-1})));
}

TEST(VirtualStack, ctor_test_2)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({ADD, SSTORE, JUMP});
    Stack stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -4);
    ASSERT_EQ(stack.max_delta(), 0);
    ASSERT_EQ(stack.delta(), -4);
    ASSERT_TRUE(test_stack_element(
        stack.get(-3), StackElemTestData{{-3}}.with_stack_offset({-3})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-2), StackElemTestData{{-2}}.with_stack_offset({-2})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1}}.with_stack_offset({-1})));
}

TEST(VirtualStack, ctor_test_3)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0, PUSH1, 0, ADD, PUSH2, 0, 0, JUMPI});
    Stack const stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), 0);
    ASSERT_EQ(stack.max_delta(), 2);
    ASSERT_EQ(stack.delta(), 0);
}

TEST(VirtualStack, ctor_test_4)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({SWAP1});
    Stack stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -2);
    ASSERT_EQ(stack.max_delta(), 0);
    ASSERT_EQ(stack.delta(), 0);
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1}}.with_stack_offset({-1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-2), StackElemTestData{{-2}}.with_stack_offset({-2})));
}

TEST(VirtualStack, ctor_test_5)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({SWAP16});
    Stack stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -17);
    ASSERT_EQ(stack.max_delta(), 0);
    ASSERT_EQ(stack.delta(), 0);
    for (int32_t i = -1; i >= -17; --i) {
        ASSERT_TRUE(test_stack_element(
            stack.get(i), StackElemTestData{{i}}.with_stack_offset({i})));
    }
}

TEST(VirtualStack, ctor_test_6)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({DUP1});
    Stack stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -1);
    ASSERT_EQ(stack.max_delta(), 1);
    ASSERT_EQ(stack.delta(), 1);
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1}}.with_stack_offset({-1})));
}

TEST(VirtualStack, ctor_test_7)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({DUP16});
    Stack stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -16);
    ASSERT_EQ(stack.max_delta(), 1);
    ASSERT_EQ(stack.delta(), 1);
    for (int32_t i = -1; i >= -16; --i) {
        ASSERT_TRUE(test_stack_element(
            stack.get(i), StackElemTestData{{i}}.with_stack_offset({i})));
    }
}

TEST(VirtualStack, ctor_test_8)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0, ADD, ISZERO, DUP1, SWAP2, SWAP1, PUSH0, PUSH0, REVERT});
    Stack stack{ir.blocks()[0]};
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -2);
    ASSERT_EQ(stack.max_delta(), 3);
    ASSERT_EQ(stack.delta(), 1);
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1}}.with_stack_offset({-1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-2), StackElemTestData{{-2}}.with_stack_offset({-2})));
}

TEST(VirtualStack, push_test)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH1, 1});
    Stack stack{ir.blocks()[0]};
    stack.push_literal(1);
    ASSERT_EQ(stack.top_index(), 0);
    ASSERT_EQ(stack.min_delta(), 0);
    ASSERT_EQ(stack.max_delta(), 1);
    ASSERT_EQ(stack.delta(), 1);
    ASSERT_TRUE(test_stack_element(
        stack.get(0), StackElemTestData{{0}}.with_literal({1})));
}

TEST(VirtualStack, pop_test)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({NOT});
    Stack stack{ir.blocks()[0]};
    auto e = stack.pop();
    ASSERT_EQ(stack.top_index(), -2);
    ASSERT_EQ(stack.min_delta(), -1);
    ASSERT_EQ(stack.max_delta(), 0);
    ASSERT_EQ(stack.delta(), 0);
    ASSERT_TRUE(
        test_stack_element(e, StackElemTestData{{}}.with_stack_offset({-1})));
}

TEST(VirtualStack, swap_test)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({SWAP2});
    Stack stack{ir.blocks()[0]};
    stack.swap(-3);
    ASSERT_EQ(stack.top_index(), -1);
    ASSERT_EQ(stack.min_delta(), -3);
    ASSERT_EQ(stack.max_delta(), 0);
    ASSERT_EQ(stack.delta(), 0);
    ASSERT_TRUE(test_stack_element(
        stack.get(-3), StackElemTestData{{-3}}.with_stack_offset({-1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-2), StackElemTestData{{-2}}.with_stack_offset({-2})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1}}.with_stack_offset({-3})));
}

TEST(VirtualStack, dup_test)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({DUP2});
    Stack stack{ir.blocks()[0]};
    stack.dup(-2);
    ASSERT_EQ(stack.top_index(), 0);
    ASSERT_EQ(stack.min_delta(), -2);
    ASSERT_EQ(stack.max_delta(), 1);
    ASSERT_EQ(stack.delta(), 1);
    ASSERT_TRUE(test_stack_element(
        stack.get(-2), StackElemTestData{{0, -2}}.with_stack_offset({-2})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1}}.with_stack_offset({-1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(0), StackElemTestData{{0, -2}}.with_stack_offset({-2})));
}

TEST(VirtualStack, push_pop_dup_swap_test_1)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        {PUSH0, DUP2, DUP2, POP, SWAP1});
    Stack stack{ir.blocks()[0]};
    stack.push_literal(0);
    stack.dup(-1);
    stack.dup(0);
    auto e = stack.pop();
    stack.swap(0);
    ASSERT_EQ(stack.top_index(), 1);
    ASSERT_EQ(stack.min_delta(), -1);
    ASSERT_EQ(stack.max_delta(), 3);
    ASSERT_EQ(stack.delta(), 2);
    ASSERT_TRUE(
        test_stack_element(e, StackElemTestData{{1}}.with_literal({0})));
    ASSERT_TRUE(test_stack_element(
        stack.get(-1), StackElemTestData{{-1, 0}}.with_stack_offset({-1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(0), StackElemTestData{{-1, 0}}.with_stack_offset({-1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(1), StackElemTestData{{1}}.with_literal({0})));
}

TEST(VirtualStack, insert_stack_offset_test_1)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0});
    Stack stack{ir.blocks()[0]};
    stack.push_literal(0);
    stack.insert_stack_offset(stack.get(0));
    ASSERT_TRUE(test_stack_element(
        stack.get(0),
        StackElemTestData{{0}}.with_literal({0}).with_stack_offset({0})));
}

TEST(VirtualStack, insert_stack_offset_test_2)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, PUSH0});
    Stack stack{ir.blocks()[0]};
    stack.push_literal(0);
    stack.push_literal(0);
    stack.push_literal(0);
    stack.insert_stack_offset(stack.get(0), 1);
    stack.insert_stack_offset(stack.get(1));
    stack.insert_stack_offset(stack.get(2));
    ASSERT_TRUE(test_stack_element(
        stack.get(0),
        StackElemTestData{{0}}.with_literal({0}).with_stack_offset({1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(1),
        StackElemTestData{{1}}.with_literal({0}).with_stack_offset({0})));
    ASSERT_TRUE(test_stack_element(
        stack.get(2),
        StackElemTestData{{2}}.with_literal({0}).with_stack_offset({2})));
}

TEST(VirtualStack, insert_stack_offset_test_3)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({PUSH0, PUSH0, PUSH0});
    Stack stack{ir.blocks()[0]};
    stack.push_literal(0);
    stack.push_literal(0);
    stack.push_literal(0);
    stack.insert_stack_offset(stack.get(0), 1);
    stack.insert_stack_offset(stack.get(2));
    stack.insert_stack_offset(stack.get(1));
    ASSERT_TRUE(test_stack_element(
        stack.get(0),
        StackElemTestData{{0}}.with_literal({0}).with_stack_offset({1})));
    ASSERT_TRUE(test_stack_element(
        stack.get(1),
        StackElemTestData{{1}}.with_literal({0}).with_stack_offset({0})));
    ASSERT_TRUE(test_stack_element(
        stack.get(2),
        StackElemTestData{{2}}.with_literal({0}).with_stack_offset({2})));
}

TEST(VirtualStack, alloc_stack_offset_test_1)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from({POP, POP});
    Stack stack{ir.blocks()[0]};
    stack.pop();
    stack.pop();
    auto e1 = stack.alloc_stack_offset(-2);
    auto e2 = stack.alloc_stack_offset(-2);
    ASSERT_TRUE(
        test_stack_element(e1, StackElemTestData{{}}.with_stack_offset({-2})));
    ASSERT_TRUE(
        test_stack_element(e2, StackElemTestData{{}}.with_stack_offset({-1})));
    stack.push(e1);
    stack.push(e2);
    ASSERT_TRUE(test_stack_element(
        e1, StackElemTestData{{-2}}.with_stack_offset({-2})));
    ASSERT_TRUE(test_stack_element(
        e2, StackElemTestData{{-1}}.with_stack_offset({-1})));
}

TEST(VirtualStack, insert_avx_reg_test_1)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        std::vector<uint8_t>(AVX_REG_COUNT + 1, POP));
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        (void)stack.insert_avx_reg(stack.get(-i - 1));
    }
    auto p = stack.insert_avx_reg(stack.get(-AVX_REG_COUNT - 1));
    ASSERT_FALSE(p.second.has_value());
    std::uint8_t rem_ix = AVX_REG_COUNT;
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        if (!stack.get(-i - 1)->avx_reg().has_value()) {
            ASSERT_TRUE(rem_ix == AVX_REG_COUNT);
            rem_ix = i;
        }
    }
    ASSERT_LT(rem_ix, AVX_REG_COUNT);
    ASSERT_EQ(stack.get(-AVX_REG_COUNT - 1)->avx_reg()->reg, rem_ix);
}

TEST(VirtualStack, insert_general_reg_test_1)
{
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(
        std::vector<uint8_t>(GENERAL_REG_COUNT + 1, POP));
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        (void)stack.insert_general_reg(stack.get(-i - 1));
    }
    auto p = stack.insert_general_reg(stack.get(-GENERAL_REG_COUNT - 1));
    ASSERT_FALSE(p.second.has_value());
    std::uint8_t rem_ix = GENERAL_REG_COUNT;
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        if (!stack.get(-i - 1)->general_reg().has_value()) {
            ASSERT_TRUE(rem_ix == GENERAL_REG_COUNT);
            rem_ix = i;
        }
    }
    ASSERT_LT(rem_ix, GENERAL_REG_COUNT);
    ASSERT_EQ(stack.get(-GENERAL_REG_COUNT - 1)->general_reg()->reg, rem_ix);
}

TEST(VirtualStack, insert_avx_reg_test_2)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i <= AVX_REG_COUNT; ++i) {
        bytecode.push_back(POP);
    }
    for (std::uint8_t i = 0; i <= AVX_REG_COUNT; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i <= AVX_REG_COUNT; ++i) {
        stack.pop();
    }
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        auto p = stack.alloc_avx_reg();
        ASSERT_EQ(std::get<0>(p)->avx_reg()->reg, i);
        stack.push(std::get<0>(p));
    }
    stack.push_literal(0);
    auto p = stack.insert_avx_reg(stack.get(-1));
    ASSERT_TRUE(p.second.has_value());
    std::uint8_t rem_ix = AVX_REG_COUNT;
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        if (!stack.get(-AVX_REG_COUNT - 1 + i)->avx_reg().has_value()) {
            ASSERT_TRUE(rem_ix == AVX_REG_COUNT);
            ASSERT_TRUE(
                stack.get(-AVX_REG_COUNT - 1 + i)->stack_offset().has_value());
            rem_ix = i;
        }
    }
    ASSERT_LT(rem_ix, AVX_REG_COUNT);
    ASSERT_EQ(stack.get(-1)->avx_reg()->reg, rem_ix);
}

TEST(VirtualStack, insert_general_reg_test_2)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i <= GENERAL_REG_COUNT; ++i) {
        bytecode.push_back(POP);
    }
    for (std::uint8_t i = 0; i <= GENERAL_REG_COUNT; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i <= GENERAL_REG_COUNT; ++i) {
        stack.pop();
    }
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        auto p = stack.alloc_general_reg();
        ASSERT_EQ(std::get<0>(p)->general_reg()->reg, i);
        stack.push(std::get<0>(p));
    }
    stack.push_literal(0);
    auto p = stack.insert_general_reg(stack.get(-1));
    ASSERT_TRUE(p.second.has_value());
    std::uint8_t rem_ix = GENERAL_REG_COUNT;
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        if (!stack.get(-GENERAL_REG_COUNT - 1 + i)->general_reg().has_value()) {
            ASSERT_TRUE(rem_ix == GENERAL_REG_COUNT);
            ASSERT_TRUE(stack.get(-GENERAL_REG_COUNT - 1 + i)
                            ->stack_offset()
                            .has_value());
            rem_ix = i;
        }
    }
    ASSERT_LT(rem_ix, GENERAL_REG_COUNT);
    ASSERT_EQ(stack.get(-1)->general_reg()->reg, rem_ix);
}

TEST(VirtualStack, insert_avx_reg_test_3)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i < AVX_REG_COUNT + 3; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    std::vector<AvxRegReserv> reservs;
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        auto p = stack.alloc_avx_reg();
        ASSERT_EQ(std::get<0>(p)->avx_reg()->reg, i);
        stack.push(std::get<0>(p));
        reservs.push_back(std::get<1>(p));
    }
    {
        stack.push_literal(0);
        reservs.pop_back();
        auto p = stack.insert_avx_reg(stack.get(AVX_REG_COUNT));
        ASSERT_EQ(stack.get(AVX_REG_COUNT)->avx_reg()->reg, AVX_REG_COUNT - 1);
        reservs.push_back(p.first);
    }
    {
        stack.push_literal(0);
        std::swap(reservs[AVX_REG_COUNT / 2], reservs.back());
        reservs.pop_back();
        auto p = stack.insert_avx_reg(stack.get(AVX_REG_COUNT + 1));
        ASSERT_EQ(
            stack.get(AVX_REG_COUNT + 1)->avx_reg()->reg, AVX_REG_COUNT / 2);
        reservs.push_back(p.first);
    }
    {
        stack.push_literal(0);
        std::swap(reservs[0], reservs.back());
        reservs.pop_back();
        auto p = stack.insert_avx_reg(stack.get(AVX_REG_COUNT + 2));
        ASSERT_EQ(stack.get(AVX_REG_COUNT + 2)->avx_reg()->reg, 0);
        reservs.push_back(p.first);
    }
}

TEST(VirtualStack, insert_general_reg_test_3)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT + 3; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    std::vector<GeneralRegReserv> reservs;
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        auto p = stack.alloc_general_reg();
        ASSERT_EQ(std::get<0>(p)->general_reg()->reg, i);
        stack.push(std::get<0>(p));
        reservs.push_back(std::get<1>(p));
    }
    {
        stack.push_literal(0);
        reservs.pop_back();
        auto p = stack.insert_general_reg(stack.get(GENERAL_REG_COUNT));
        ASSERT_EQ(
            stack.get(GENERAL_REG_COUNT)->general_reg()->reg,
            GENERAL_REG_COUNT - 1);
        reservs.push_back(p.first);
    }
    {
        stack.push_literal(0);
        std::swap(reservs[GENERAL_REG_COUNT / 2], reservs.back());
        reservs.pop_back();
        auto p = stack.insert_general_reg(stack.get(GENERAL_REG_COUNT + 1));
        ASSERT_EQ(
            stack.get(GENERAL_REG_COUNT + 1)->general_reg()->reg,
            GENERAL_REG_COUNT / 2);
        reservs.push_back(p.first);
    }
    {
        stack.push_literal(0);
        std::swap(reservs[0], reservs.back());
        reservs.pop_back();
        auto p = stack.insert_general_reg(stack.get(GENERAL_REG_COUNT + 2));
        ASSERT_EQ(stack.get(GENERAL_REG_COUNT + 2)->general_reg()->reg, 0);
        reservs.push_back(p.first);
    }
}

TEST(VirtualStack, spill_all_avx_regs_test_1)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        auto p = stack.alloc_avx_reg();
        ASSERT_EQ(std::get<0>(p)->avx_reg()->reg, i);
        stack.push(std::get<0>(p));
    }
    auto ups = stack.spill_all_avx_regs();
    ASSERT_EQ(ups.size(), AVX_REG_COUNT);
    for (std::uint8_t i = 0; i < AVX_REG_COUNT; ++i) {
        ASSERT_EQ(ups[i].first.reg, i);
        ASSERT_EQ(ups[i].second.offset, i);
    }
}

TEST(VirtualStack, spill_all_caller_save_general_regs_test_1)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT; ++i) {
        auto p = stack.alloc_general_reg();
        ASSERT_EQ(std::get<0>(p)->general_reg()->reg, i);
        stack.push(std::get<0>(p));
    }
    auto ups = stack.spill_all_caller_save_general_regs();
    ASSERT_EQ(ups.size(), GENERAL_REG_COUNT - 1);
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT - 1; ++i) {
        ASSERT_EQ(ups[i].first.reg, i + 1);
        ASSERT_EQ(ups[i].second.offset, i + 1);
    }
}

TEST(VirtualStack, spill_all_avx_regs_test_2)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i < AVX_REG_COUNT - 1; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i < AVX_REG_COUNT - 1; ++i) {
        auto p = stack.alloc_avx_reg();
        ASSERT_EQ(std::get<0>(p)->avx_reg()->reg, i);
        stack.push(std::get<0>(p));
    }
    auto ups = stack.spill_all_avx_regs();
    ASSERT_EQ(ups.size(), AVX_REG_COUNT - 1);
    for (std::uint8_t i = 0; i < AVX_REG_COUNT - 1; ++i) {
        ASSERT_EQ(ups[i].first.reg, i);
        ASSERT_EQ(ups[i].second.offset, i);
    }
}

TEST(VirtualStack, spill_all_caller_save_general_regs_test_2)
{
    std::vector<uint8_t> bytecode;
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT - 1; ++i) {
        bytecode.push_back(PUSH0);
    }
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT - 1; ++i) {
        auto p = stack.alloc_general_reg();
        ASSERT_EQ(std::get<0>(p)->general_reg()->reg, i);
        stack.push(std::get<0>(p));
    }
    auto ups = stack.spill_all_caller_save_general_regs();
    ASSERT_EQ(ups.size(), GENERAL_REG_COUNT - 2);
    for (std::uint8_t i = 0; i < GENERAL_REG_COUNT - 2; ++i) {
        ASSERT_EQ(ups[i].first.reg, i + 1);
        ASSERT_EQ(ups[i].second.offset, i + 1);
    }
}

TEST(VirtualStack, deferred_comparison_test_1)
{
    std::vector<uint8_t> bytecode = {PUSH0, POP};
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};
    ASSERT_FALSE(stack.has_deferred_comparison_at(0));
    stack.push_deferred_comparison(Comparison::Below);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    auto dc = stack.discharge_deferred_comparison();
    ASSERT_EQ(dc.stack_elem, stack.get(0).get());
    ASSERT_EQ(dc.negated_stack_elem, nullptr);
    ASSERT_EQ(dc.comparison(), Comparison::Below);
}

TEST(VirtualStack, deferred_comparison_test_2)
{
    std::vector<uint8_t> bytecode = {PUSH0, PUSH0, POP, POP};
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};

    ASSERT_FALSE(stack.has_deferred_comparison_at(0));

    stack.push_deferred_comparison(Comparison::BelowEqual);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));

    stack.push_literal(0);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_FALSE(stack.has_deferred_comparison_at(1));

    auto e1 = stack.pop();
    auto e2 = stack.negate_if_deferred_comparison(e1);
    ASSERT_FALSE(e2);
    stack.push(std::move(e1));
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_FALSE(stack.has_deferred_comparison_at(1));

    stack.pop();
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_FALSE(stack.has_deferred_comparison_at(1));

    e1 = stack.pop();
    e2 = stack.negate_if_deferred_comparison(std::move(e1));
    ASSERT_TRUE(e2);
    stack.push(std::move(e2));
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));

    auto dc = stack.discharge_deferred_comparison();
    ASSERT_EQ(dc.stack_elem, nullptr);
    ASSERT_EQ(dc.negated_stack_elem, stack.get(0).get());
    ASSERT_EQ(dc.comparison(), Comparison::BelowEqual);
}

TEST(VirtualStack, deferred_comparison_test_3)
{
    std::vector<uint8_t> bytecode = {
        PUSH0, DUP1, PUSH0, DUP2, POP, POP, POP, POP};
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};

    ASSERT_FALSE(stack.has_deferred_comparison_at(0));

    stack.push_deferred_comparison(Comparison::Greater);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));

    stack.dup(0);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));

    stack.push_literal(0);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));
    ASSERT_FALSE(stack.has_deferred_comparison_at(2));

    stack.dup(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0));
    ASSERT_TRUE(stack.has_deferred_comparison_at(1));
    ASSERT_FALSE(stack.has_deferred_comparison_at(2));
    ASSERT_TRUE(stack.has_deferred_comparison_at(3));

    auto dc = stack.discharge_deferred_comparison();
    ASSERT_EQ(dc.stack_elem, stack.get(0).get());
    ASSERT_EQ(dc.stack_elem, stack.get(1).get());
    ASSERT_NE(dc.stack_elem, stack.get(2).get());
    ASSERT_EQ(dc.stack_elem, stack.get(3).get());
    ASSERT_EQ(dc.negated_stack_elem, nullptr);
    ASSERT_EQ(dc.comparison(), Comparison::Greater);
}

TEST(VirtualStack, deferred_comparison_test_4)
{
    std::vector<uint8_t> bytecode = {
        PUSH0, DUP1, PUSH0, DUP2, DUP1, SWAP3, SWAP1};
    auto ir = basic_blocks::BasicBlocksIR::unsafe_from(bytecode);
    Stack stack{ir.blocks()[0]};

    ASSERT_FALSE(stack.has_deferred_comparison_at(0));

    stack.push_deferred_comparison(Comparison::Greater);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT

    stack.dup(0);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // GT

    stack.push_literal(0);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // GT
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0

    stack.dup(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // GT
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(3)); // GT

    auto e1 = stack.pop();
    auto e2 = stack.negate_if_deferred_comparison(std::move(e1));
    ASSERT_TRUE(e2);
    stack.push(std::move(e2));
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // GT
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(3)); // LE

    stack.dup(3);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // GT
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(3)); // LE
    ASSERT_TRUE(stack.has_deferred_comparison_at(4)); // LE

    stack.swap(1);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // LE
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(3)); // LE
    ASSERT_TRUE(stack.has_deferred_comparison_at(4)); // GT

    e1 = stack.pop();
    e2 = stack.negate_if_deferred_comparison(std::move(e1));
    ASSERT_TRUE(e2);
    stack.push(std::move(e2));
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // LE
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(3)); // LE
    ASSERT_TRUE(stack.has_deferred_comparison_at(4)); // LE

    stack.swap(3);
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // LE
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(3)); // LE
    ASSERT_TRUE(stack.has_deferred_comparison_at(4)); // LE

    e1 = stack.pop();
    e2 = stack.negate_if_deferred_comparison(std::move(e1));
    ASSERT_TRUE(e2);
    stack.push(std::move(e2));
    ASSERT_TRUE(stack.has_deferred_comparison_at(0)); // GT
    ASSERT_TRUE(stack.has_deferred_comparison_at(1)); // LE
    ASSERT_FALSE(stack.has_deferred_comparison_at(2)); // 0
    ASSERT_TRUE(stack.has_deferred_comparison_at(3)); // LE
    ASSERT_TRUE(stack.has_deferred_comparison_at(4)); // GT

    auto dc = stack.discharge_deferred_comparison();
    ASSERT_EQ(dc.stack_elem, stack.get(0).get());
    ASSERT_EQ(dc.negated_stack_elem, stack.get(1).get());
    ASSERT_NE(dc.stack_elem, stack.get(2).get());
    ASSERT_NE(dc.negated_stack_elem, stack.get(2).get());
    ASSERT_EQ(dc.negated_stack_elem, stack.get(3).get());
    ASSERT_EQ(dc.stack_elem, stack.get(4).get());
    ASSERT_EQ(dc.comparison(), Comparison::Greater);
}
