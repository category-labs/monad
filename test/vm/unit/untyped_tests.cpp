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
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed.hpp>
#include <category/vm/compiler/ir/untyped.hpp>

#include <category/vm/evm/opcodes.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <variant>
#include <vector>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::untyped;

TEST(untyped, test_invalid)
{
    auto ir = poly_typed::PolyTypedIR(local_stacks::LocalStacksIR(
        basic_blocks::BasicBlocksIR::unsafe_from({ADD})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_FALSE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
}

TEST(untyped, dead_code)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {PUSH0, STOP, JUMPDEST, PUSH0, SLOAD, JUMP})));
    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 2);
    ASSERT_TRUE(std::holds_alternative<DeadCode>(blocks[1].terminator));
}

TEST(untyped, unsupported_sload_jump)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {JUMPDEST, PUSH0, SLOAD, JUMP})));
    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_FALSE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
}

TEST(untyped, test_computed_literal_jump)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {PUSH1, 5, PUSH1, 1, ADD, JUMP, JUMPDEST, STOP})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 2);
    ASSERT_TRUE(std::holds_alternative<Jump>(blocks[0].terminator));

    auto const &jump = std::get<Jump>(blocks[0].terminator);
    ASSERT_TRUE(std::holds_alternative<block_id>(jump.jump_dest));
}

TEST(untyped, test_jumpi_word_cont)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {JUMPDEST, PUSH1, 0xc,    PUSH0, PUSH1,    0xe,      JUMPI,
             JUMPDEST, PUSH1, 0x12,   SWAP1, JUMP,     JUMPDEST, JUMP,
             JUMPDEST, PUSH0, SSTORE, STOP,  JUMPDEST, STOP})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 5);
    ASSERT_TRUE(std::holds_alternative<JumpI>(blocks[0].terminator));

    // in the fallthrough case, we coerce the evm word to address
    // as it will be jumped to.
    // but in the if case, the address will be SSTOREd, so it should not
    // be coerced
    auto const &jumpi = std::get<JumpI>(blocks[0].terminator);
    ASSERT_EQ(jumpi.coerce_to_addr.size(), 0);
    ASSERT_EQ(jumpi.fallthrough_coerce_to_addr.size(), 1);
    ASSERT_EQ(jumpi.fallthrough_coerce_to_addr[0], 0);
}

TEST(untyped, test_jump_coerce_multiple)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {JUMPDEST, PUSH1, 0xe,      DUP1,  PUSH1,  0x9,   PUSH1,
             0xe,      JUMP,  JUMPDEST, PUSH1, 0x10,   SWAP1, JUMP,
             JUMPDEST, JUMP,  JUMPDEST, PUSH0, SSTORE, STOP})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 4);
    ASSERT_TRUE(std::holds_alternative<Jump>(blocks[0].terminator));

    auto const &jump = std::get<Jump>(blocks[0].terminator);
    ASSERT_EQ(jump.coerce_to_addr.size(), 2);
    ASSERT_EQ(jump.coerce_to_addr[0], 0);
    ASSERT_EQ(jump.coerce_to_addr[1], 1);
}

TEST(untyped, test_jump_word)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {JUMPDEST,
             PUSH1,
             0xb,
             PUSH1,
             0x6,
             JUMP,
             JUMPDEST,
             DUP1,
             DUP1,
             SSTORE,
             JUMP,
             JUMPDEST,
             STOP})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 3);
    ASSERT_TRUE(std::holds_alternative<Jump>(blocks[1].terminator));

    auto const &jump = std::get<Jump>(blocks[1].terminator);
    // because the top of the stack value passed into this block
    // is used both as a jump destination and as
    // an EVM word for sstore, it must be an EVM word and cannot be
    // cast to an address until the JUMP
    ASSERT_TRUE(std::holds_alternative<Word>(jump.jump_dest));
}

TEST(untyped, test_jump_addr)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {// 0x0:
             JUMPDEST,
             PUSH1,
             0xf,
             PUSH1,
             0x6,
             JUMP,

             // 0x6 : (Word : s0 -> Exit),s0 -> Exit
             JUMPDEST,
             DUP1,
             PUSH1,
             0xb,
             JUMP, // : Word,(s0 -> Exit),s0 -> Exit <- we must coerce here
                   // because the duplicated input changed from a WordCont to
                   // Cont, due to the jump to 0xb

             // 0xb : Word,(s0 -> Exit),s0 -> Exit
             JUMPDEST,
             DUP1,
             SSTORE,
             JUMP,

             // 0xf: s0 -> Exit
             JUMPDEST,
             STOP})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 4);
    ASSERT_TRUE(std::holds_alternative<Jump>(blocks[1].terminator));

    auto const &jump = std::get<Jump>(blocks[1].terminator);
    ASSERT_EQ(jump.coerce_to_addr.size(), 1);
    ASSERT_EQ(jump.coerce_to_addr[0], 1);

    ASSERT_TRUE(std::holds_alternative<Jump>(blocks[2].terminator));

    auto const &jump2 = std::get<Jump>(blocks[2].terminator);
    ASSERT_TRUE(std::holds_alternative<Addr>(jump2.jump_dest));
}

TEST(untyped, dead_cont_words)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {STOP,
             JUMPDEST, // this block has type Word... -> Exit, hence we mark it
                       // as dead code because the entry-point has a valid type
                       // of s0 -> Exit
             DUP1,
             DUP1,
             SSTORE,
             DUP1,
             DUP1,
             JUMPI,
             JUMP})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 3);
    ASSERT_TRUE(std::holds_alternative<DeadCode>(blocks[1].terminator));
}

TEST(untyped, pad_output_stack)
{
    auto ir = poly_typed::PolyTypedIR(
        local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR::unsafe_from(
            {PUSH1,
             0xf,
             PUSH1,
             0xf,
             PUSH1,
             0x7,
             JUMP,

             // 0x7 : Word,(Word : s1 -> Exit),s1 -> Exit
             JUMPDEST,
             PUSH1,
             0xb,
             JUMP, // here the output stack is only a single value, but the
                   // output stack type is Word,(Word : s1 -> Exit),s1 -> Exit,
                   // hence we need to pad out theoutput stack to 0xb, %p0, %p1

             // 0xb : Word,(Word : s0 -> Exit),s0 -> Exit
             JUMPDEST,
             DUP2,
             SSTORE,
             JUMP,

             // 0xf : s0 -> Exit
             JUMPDEST,
             STOP})));

    auto blocks_may = build_untyped(ir.jumpdests, std::move(ir.blocks));
    ASSERT_TRUE(
        std::holds_alternative<std::vector<untyped::Block>>(blocks_may));
    auto const &blocks = std::get<std::vector<untyped::Block>>(blocks_may);
    ASSERT_EQ(blocks.size(), 4);
}
