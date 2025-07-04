#include <monad/vm/compiler/ir/basic_blocks.hpp>
#include <monad/vm/compiler/ir/instruction.hpp>
#include <monad/vm/compiler/ir/local_stacks.hpp>
#include <monad/vm/compiler/types.hpp>
#include <monad/vm/evm/opcodes.hpp>

#include <evmc/evmc.h>

#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <unordered_map>
#include <utility>
#include <vector>

using namespace monad::vm::compiler;
using namespace intx;

template <
    typename Op, typename... Args,
    evmc_revision Rev = EVMC_LATEST_STABLE_REVISION>
Instruction i(std::uint32_t pc, Op evm_opcode, Args &&...args)
{
    auto info = opcode_table<Rev>[evm_opcode];
    return Instruction(
        pc,
        basic_blocks::evm_op_to_opcode(evm_opcode),
        std::forward<Args>(args)...,
        info.min_gas,
        info.min_stack,
        info.index,
        info.stack_increase,
        info.dynamic_gas);
}

void blocks_eq(
    std::vector<uint8_t> const &in,
    std::unordered_map<byte_offset, block_id> const &expected_jumpdests,
    std::vector<basic_blocks::Block> const &expected_blocks)
{
    basic_blocks::BasicBlocksIR const actual(in);

    EXPECT_EQ(actual.jump_dests(), expected_jumpdests);
    EXPECT_EQ(actual.blocks(), expected_blocks);
}

using enum basic_blocks::Terminator;

TEST(TerminatorTest, Formatter)
{
    EXPECT_EQ(std::format("{}", FallThrough), "FallThrough");
    EXPECT_EQ(std::format("{}", JumpI), "JumpI");
    EXPECT_EQ(std::format("{}", Jump), "Jump");
    EXPECT_EQ(std::format("{}", Return), "Return");
    EXPECT_EQ(std::format("{}", Revert), "Revert");
    EXPECT_EQ(std::format("{}", SelfDestruct), "SelfDestruct");
    EXPECT_EQ(std::format("{}", Stop), "Stop");
    EXPECT_EQ(std::format("{}", InvalidInstruction), "InvalidInstruction");
}

TEST(BasicBlocksTest, ToBlocks)
{
    blocks_eq(
        {},
        {},
        {
            {{}, Stop, INVALID_BLOCK_ID},
        });

    blocks_eq(
        {STOP},
        {},
        {
            {{}, Stop, INVALID_BLOCK_ID},
        });

    blocks_eq(
        {0xEE},
        {},
        {
            {{}, InvalidInstruction, INVALID_BLOCK_ID},
        });

    blocks_eq(
        {PUSH1},
        {},
        {
            {{
                 i(0, PUSH1),
             },
             Stop,
             INVALID_BLOCK_ID},
        });

    blocks_eq(
        {PUSH2, 0xf},
        {},
        {
            {{
                 i(0, PUSH2, 0xf00),
             },
             Stop,
             INVALID_BLOCK_ID},
        });

    blocks_eq(
        {STOP, ADD},
        {},
        {
            {{}, Stop, INVALID_BLOCK_ID},
        });

    blocks_eq(
        {JUMPDEST, STOP},
        {{0, 0}},
        {
            {{}, Stop, INVALID_BLOCK_ID},
        });

    blocks_eq(
        {ADD, REVERT},
        {},
        {
            {{
                 i(0, ADD),
             },
             Revert,
             INVALID_BLOCK_ID},
        });

    blocks_eq(
        {ADD, ADD, RETURN},
        {},
        {
            {{
                 i(0, ADD),
                 i(1, ADD),
             },
             Return,
             INVALID_BLOCK_ID},
        });

    blocks_eq(
        {JUMPDEST, ADD, REVERT},
        {{0, 0}},
        {
            {{
                 i(1, ADD),
             },
             Revert,
             INVALID_BLOCK_ID},
        });

    blocks_eq(
        {JUMPI},
        {},
        {
            {{}, JumpI, 1},
            {{}, Stop, INVALID_BLOCK_ID, 1},
        });

    blocks_eq(
        {JUMPDEST, JUMPDEST},
        {{0, 0}, {1, 1}},
        {
            {{}, FallThrough, 1, 0},
            {{}, Stop, INVALID_BLOCK_ID, 1},
        });

    blocks_eq(
        {JUMPDEST, JUMPDEST, JUMPDEST},
        {{0, 0}, {1, 1}, {2, 2}},
        {
            {{}, FallThrough, 1, 0},
            {{}, FallThrough, 2, 1},
            {{}, Stop, INVALID_BLOCK_ID, 2},
        });

    blocks_eq(
        {JUMPDEST, ADD, JUMPDEST},
        {{0, 0}, {2, 1}},
        {
            {{
                 i(1, ADD),
             },
             FallThrough,
             1,
             0},
            {{}, Stop, INVALID_BLOCK_ID, 2},
        });

    blocks_eq(
        {ADD, ADD, JUMP, ADD, JUMPDEST, SELFDESTRUCT},
        {{4, 1}},
        {
            {{
                 i(0, ADD),
                 i(1, ADD),
             },
             Jump,
             INVALID_BLOCK_ID},
            {{}, SelfDestruct, INVALID_BLOCK_ID, 4},
        });

    blocks_eq(
        {ADD, ADD, JUMP, ADD, JUMPDEST, JUMPDEST, SELFDESTRUCT},
        {{4, 1}, {5, 2}},
        {
            {{
                 i(0, ADD),
                 i(1, ADD),
             },
             Jump,
             INVALID_BLOCK_ID},
            {{}, FallThrough, 2, 4},
            {{}, SelfDestruct, INVALID_BLOCK_ID, 5},
        });
}

TEST(BlockTest, Formatter)
{
    EXPECT_EQ(
        std::format("{}", basic_blocks::Block{{}, Return, INVALID_BLOCK_ID}),
        "  0x00:\n    Return\n");

    EXPECT_EQ(
        std::format(
            "{}",
            basic_blocks::Block{
                {
                    i(0, ADD),
                    i(1, ADD),
                },
                SelfDestruct,
                INVALID_BLOCK_ID}),
        "  0x00:\n      ADD\n      ADD\n    SelfDestruct\n");

    EXPECT_EQ(
        std::format(
            "{}",
            basic_blocks::Block{
                {
                    i(1, ADD),
                },
                JumpI,
                0}),
        "  0x00:\n      ADD\n    JumpI 0\n");
}

auto const instrIR0 = basic_blocks::BasicBlocksIR({});
auto const instrIR1 =
    basic_blocks::BasicBlocksIR({JUMPDEST, SUB, SUB, JUMPDEST});
auto const instrIR2 =
    basic_blocks::BasicBlocksIR({JUMPDEST, JUMPDEST, SUB, JUMPDEST});
auto const instrIR3 = basic_blocks::BasicBlocksIR(
    {PUSH1,    255,      PUSH1, 14,    SWAP2, PUSH1, 17,       JUMPI,
     JUMPDEST, PUSH1,    1,     ADD,   SWAP1, JUMP,  JUMPDEST, POP,
     STOP,     JUMPDEST, SWAP1, PUSH1, 8,     JUMP});

TEST(BasicBlocksIRTest, Validation)
{
    EXPECT_TRUE(instrIR0.is_valid());
    EXPECT_TRUE(instrIR1.is_valid());
    EXPECT_TRUE(instrIR2.is_valid());
    EXPECT_TRUE(instrIR3.is_valid());
}

TEST(BasicBlocksIRTest, Formatter)
{
    EXPECT_EQ(
        std::format("{}", instrIR0),
        R"(basic_blocks:
  block 0  0x00:
    Stop

  jumpdests:
)");

    EXPECT_EQ(
        std::format("{}", instrIR1),
        R"(basic_blocks:
  block 0  0x00:
      SUB
      SUB
    FallThrough 1
  block 1  0x03:
    Stop

  jumpdests:
    3:1
    0:0
)");

    EXPECT_EQ(
        std::format("{}", instrIR2),
        R"(basic_blocks:
  block 0  0x00:
    FallThrough 1
  block 1  0x01:
      SUB
    FallThrough 2
  block 2  0x03:
    Stop

  jumpdests:
    3:2
    1:1
    0:0
)");

    EXPECT_EQ(
        std::format("{}", instrIR3),
        R"(basic_blocks:
  block 0  0x00:
      PUSH1 0xff
      PUSH1 0xe
      SWAP2
      PUSH1 0x11
    JumpI 1
  block 1  0x08:
      PUSH1 0x1
      ADD
      SWAP1
    Jump
  block 2  0x0e:
      POP
    Stop
  block 3  0x11:
      SWAP1
      PUSH1 0x8
    Jump

  jumpdests:
    17:3
    14:2
    8:1
)");
}

local_stacks::Value lit(uint256_t x)
{
    return local_stacks::Value{local_stacks::ValueIs::LITERAL, x};
}

local_stacks::Value param_id(uint256_t x)
{
    return local_stacks::Value{local_stacks::ValueIs::PARAM_ID, x};
}

local_stacks::Value computed()
{
    return local_stacks::Value{local_stacks::ValueIs::COMPUTED, 0};
}

TEST(LocalStacksValueTest, Formatter)
{
    EXPECT_EQ(std::format("{}", lit(0x42)), "0x42");
    EXPECT_EQ(std::format("{}", param_id(42)), "%p42");
    EXPECT_EQ(std::format("{}", computed()), "COMPUTED");
}

TEST(LocalStacksBlock, Formatter)
{
    local_stacks::Block blk = {0, {}, {}, Stop, INVALID_BLOCK_ID, 0};

    EXPECT_EQ(
        std::format("{}", blk),
        R"(    min_params: 0
    Stop
    output: [ ]
)");

    local_stacks::Block blk1 = {1, {computed()}, {}, Stop, INVALID_BLOCK_ID, 0};

    EXPECT_EQ(
        std::format("{}", blk1),
        R"(    min_params: 1
    Stop
    output: [ COMPUTED ]
)");

    local_stacks::Block blk2 = {
        2, {computed(), param_id(0), lit(0x42)}, {}, Stop, INVALID_BLOCK_ID, 0};
    EXPECT_EQ(
        std::format("{}", blk2),
        R"(    min_params: 2
    Stop
    output: [ COMPUTED %p0 0x42 ]
)");
}

TEST(LocalStacksIR, Formatter)
{
    EXPECT_EQ(
        std::format("{}", local_stacks::LocalStacksIR(std::move(instrIR0))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 0
    Stop
    output: [ ]

  jumpdests:
)");

    EXPECT_EQ(
        std::format("{}", local_stacks::LocalStacksIR(std::move(instrIR1))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 3
      SUB
      SUB
    FallThrough 1
    output: [ COMPUTED ]
  block 1 - 0x3:
    min_params: 0
    Stop
    output: [ ]

  jumpdests:
    3:1
    0:0
)");

    EXPECT_EQ(
        std::format("{}", local_stacks::LocalStacksIR(std::move(instrIR2))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 0
    FallThrough 1
    output: [ ]
  block 1 - 0x1:
    min_params: 2
      SUB
    FallThrough 2
    output: [ COMPUTED ]
  block 2 - 0x3:
    min_params: 0
    Stop
    output: [ ]

  jumpdests:
    3:2
    1:1
    0:0
)");

    EXPECT_EQ(
        std::format(
            "{}",
            local_stacks::LocalStacksIR(basic_blocks::BasicBlocksIR(
                {PUSH0,
                 PUSH1,
                 0xa,
                 PC,
                 ADDRESS,
                 ADD,
                 PC,
                 DUP1,
                 DUP3,
                 SWAP1,
                 POP,
                 SWAP4,
                 DUP6,
                 SWAP7}))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 2
      PUSH0
      PUSH1 0xa
      PC
      ADDRESS
      ADD
      PC
      DUP1
      DUP3
      SWAP1
      POP
      SWAP4
      DUP6
      SWAP7
    Stop
    output: [ %p1 0x0 0x6 COMPUTED 0xa COMPUTED %p0 %p0 ]

  jumpdests:
)");

    EXPECT_EQ(
        std::format(
            "{}",
            local_stacks::LocalStacksIR(
                basic_blocks::BasicBlocksIR({PUSH1, 0xb, CODESIZE, ADD}))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 0
      PUSH1 0xb
      CODESIZE
      ADD
    Stop
    output: [ 0xf ]

  jumpdests:
)");

    EXPECT_EQ(
        std::format(
            "{}",
            local_stacks::LocalStacksIR(
                basic_blocks::BasicBlocksIR({PUSH0, ISZERO}))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 0
      PUSH0
      ISZERO
    Stop
    output: [ 0x1 ]

  jumpdests:
)");

    EXPECT_EQ(
        std::format(
            "{}",
            local_stacks::LocalStacksIR(
                basic_blocks::BasicBlocksIR({PUSH1, 0x2, PUSH1, 0x1, LT}))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 0
      PUSH1 0x2
      PUSH1 0x1
      LT
    Stop
    output: [ 0x1 ]

  jumpdests:
)");

    EXPECT_EQ(
        std::format(
            "{}",
            local_stacks::LocalStacksIR(
                basic_blocks::BasicBlocksIR({PUSH1, 0x2, PUSH1, 0x1, GT}))),
        R"(local_stacks:
  block 0 - 0x0:
    min_params: 0
      PUSH1 0x2
      PUSH1 0x1
      GT
    Stop
    output: [ 0x0 ]

  jumpdests:
)");
}
