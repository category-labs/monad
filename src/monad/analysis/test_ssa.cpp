#include <monad/analysis/analysis_fmt.hpp>
#include <monad/analysis/ssa.hpp>
#include <monad/analysis/ssa_fmt.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/variant.hpp>

#include <gtest/gtest.h>

#include <tl/expected.hpp>

using namespace monad::analysis;
using enum evmone::Opcode;
using namespace evmc::literals;

tl::expected<bool, std::string>
expect_eq_helper(SSAControlFlowGraph const &a, SSAControlFlowGraph const &b)
{
    if (a.size() != b.size()) {
        return tl::unexpected{
            std::string{"these CFGs are of different sizes!"}};
    }

    for (auto const &[block_index, basic_block] : a) {
        if (basic_block != b.at(block_index)) {
            if (basic_block.instructions != b.at(block_index).instructions) {
                return tl::unexpected{fmt::format(
                    "instruction mismatch at block_index: {} expected {} but "
                    "got {}",
                    block_index,
                    basic_block,
                    b.at(block_index))};
            }
            if (basic_block.control_flow != b.at(block_index).control_flow) {
                return tl::unexpected{fmt::format(
                    "control flow mismatch at block_index: {} expected {} but "
                    "got {}",
                    block_index,
                    basic_block,
                    b.at(block_index))};
            }
            if (basic_block.stack != b.at(block_index).stack) {
                return tl::unexpected{fmt::format(
                    "stack mismatch at block_index: {} expected {} but got {}",
                    block_index,
                    basic_block,
                    b.at(block_index))};
            }

            return tl::unexpected{fmt::format(
                "mismatch at block_index: {} expected {} but got {}",
                block_index,
                basic_block,
                b.at(block_index))};
        }
    }

    return true;
}

TEST(LiftCFGToSSA, SingleBasicBlock)
{
    ControlFlowGraph control_flow_graph{
        {0,
         BasicBlock{
             Instructions{
                 Instruction{0x00, OP_PUSH1, 0x80_bytes32},
                 Instruction{0x02, OP_PUSH1, 0x40_bytes32},
                 Instruction{0x04, OP_MSTORE},
                 Instruction{0x05, OP_CALLVALUE},
                 Instruction{0x06, OP_DUP1},
                 Instruction{0x07, OP_ISZERO},
                 Instruction{0x08, OP_PUSH1, 0x0f_bytes32},
                 Instruction{0x0a, OP_JUMPI}},
             ControlFlow{Halting{}}}}};
    auto ssa = lift_cfg_to_ssa(control_flow_graph);
    std::cout << fmt::format("{}", ssa) << std::endl;

    auto expected_ssa = SSAControlFlowGraph{
        {0,
         SSABasicBlock{
             SSAInstructions{
                 SSAInstruction{
                     0x00,
                     OP_PUSH1,
                     Arguments{StackValue{ConcreteValue{0x80_bytes32}}},
                     0},
                 SSAInstruction{
                     0x02,
                     OP_PUSH1,
                     Arguments{StackValue{ConcreteValue{0x40_bytes32}}},
                     1},
                 SSAInstruction{
                     0x04,
                     OP_MSTORE,
                     Arguments{
                         StackValue{Register{1}}, StackValue{Register{0}}},
                     std::nullopt},
                 SSAInstruction{0x05, OP_CALLVALUE, Arguments{}, 2},
                 SSAInstruction{
                     0x07,
                     OP_ISZERO,
                     Arguments{StackValue{Register{2}}},
                     std::nullopt},
                 SSAInstruction{
                     0x08,
                     OP_PUSH1,
                     Arguments{StackValue{ConcreteValue{0x0f_bytes32}}},
                     3},
                 SSAInstruction{
                     0x0a,
                     OP_JUMPI,
                     Arguments{
                         StackValue{Register{3}}, StackValue{Register{2}}},
                     std::nullopt}},
             ControlFlow{Halting{}},
             SymbolicStack{StackValue{PlaceholderValue{-32}},
                           StackValue{PlaceholderValue{-31}},
                           StackValue{PlaceholderValue{-30}},
                           StackValue{PlaceholderValue{-29}},
                           StackValue{PlaceholderValue{-28}},
                           StackValue{PlaceholderValue{-27}},
                           StackValue{PlaceholderValue{-26}},
                           StackValue{PlaceholderValue{-25}},
                           StackValue{PlaceholderValue{-24}},
                           StackValue{PlaceholderValue{-23}},
                           StackValue{PlaceholderValue{-22}},
                           StackValue{PlaceholderValue{-21}},
                           StackValue{PlaceholderValue{-20}},
                           StackValue{PlaceholderValue{-19}},
                           StackValue{PlaceholderValue{-18}},
                           StackValue{PlaceholderValue{-17}},
                           StackValue{PlaceholderValue{-16}},
                           StackValue{PlaceholderValue{-15}},
                           StackValue{PlaceholderValue{-14}},
                           StackValue{PlaceholderValue{-13}},
                           StackValue{PlaceholderValue{-12}},
                           StackValue{PlaceholderValue{-11}},
                           StackValue{PlaceholderValue{-10}},
                           StackValue{PlaceholderValue{-9}},
                           StackValue{PlaceholderValue{-8}},
                           StackValue{PlaceholderValue{-7}},
                           StackValue{PlaceholderValue{-6}},
                           StackValue{PlaceholderValue{-5}},
                           StackValue{PlaceholderValue{-4}},
                           StackValue{PlaceholderValue{-3}},
                           StackValue{PlaceholderValue{-2}},
                           StackValue{PlaceholderValue{-1}}}}

        }};

    auto res = expect_eq_helper(expected_ssa, ssa);
    EXPECT_TRUE(res.has_value()) << res.error();
}
