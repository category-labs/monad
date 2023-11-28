#include <monad/analysis/ssa.hpp>

#include <gtest/gtest.h>

using namespace monad::analysis;
using enum evmone::Opcode;
using namespace evmc::literals;

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
}
