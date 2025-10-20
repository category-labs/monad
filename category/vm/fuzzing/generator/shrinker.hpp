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

#pragma once

#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/fuzzing/generator/choice.hpp>
#include <category/vm/fuzzing/generator/data.hpp>
#include <category/vm/fuzzing/generator/instruction_data.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <array>
#include <iostream>
#include <limits>
#include <memory>
#include <random>
#include <unordered_set>
#include <variant>
#include <vector>

using namespace evmc::literals;

namespace monad::vm::fuzzing
{
    template <typename Engine, typename T>
    std::pair<std::vector<T>, std::size_t>
    erase_element(Engine &engine, std::vector<T> vec)
    {
        MONAD_VM_ASSERT(vec.size() != 0);

        auto const element_to_remove = std::uniform_int_distribution<size_t>(
            0, static_cast<size_t>(vec.size()) - 1)(engine);

        vec.erase(vec.begin() + static_cast<ptrdiff_t>(element_to_remove));
        return {vec, static_cast<std::size_t>(element_to_remove)};
    }

    template <typename Engine, typename T>
    std::vector<T>
    erase_range(Engine &engine, std::vector<T> vec, double mean_ratio)
    {
        MONAD_VM_ASSERT(vec.size() != 0);

        // Generate ranges of instructions to remove.
        // Using a geometric distribution of parameter p where mean = 1/p
        // mean_ratio is the ratio of the mean to the total size of the vector.
        // e.g. mean_ratio = 0.1 means the mean is 10% of the vector size.
        // So p = 1/(mean_ratio * vec.size())
        auto const p = 1 / (mean_ratio * static_cast<double>(vec.size()));

        if (p >= 1.0) {
            // Invalid p, just remove a single element
            return erase_element(engine, std::move(vec)).first;
        }
        else {
            auto range_size_dist = std::geometric_distribution<std::size_t>(p);
            auto range_size = std::min<std::size_t>(
                range_size_dist(engine) + 1, vec.size() - 1);
            auto range_start = std::uniform_int_distribution<std::size_t>(
                0, vec.size() - range_size)(engine);

            vec.erase(
                vec.begin() + static_cast<ptrdiff_t>(range_start),
                vec.begin() + static_cast<ptrdiff_t>(range_start + range_size));
            return vec;
        }
    }

    template <typename Engine>
    std::pair<std::vector<BasicBlock>, std::size_t>
    shrink_contract(Engine &engine, std::vector<BasicBlock> blocks)
    {
        MONAD_VM_ASSERT(blocks.size() != 0);

        auto [new_blocks, removed_block] =
            erase_element(engine, std::move(blocks));

        // We need to adjust jump destinations so they still point to their
        // original targets. Push instructions with a ValidJumpDest operand must
        // be decremented if they point to a block after the removed one.
        for (auto &block : new_blocks) {
            for (auto &instr : block.instructions) {
                if (auto *push = std::get_if<Push>(&instr)) {
                    if (auto *vjd = std::get_if<ValidJumpDest>(push)) {
                        if (auto *bix = std::get_if<BlockIx>(vjd)) {
                            if (bix->index != 0 &&
                                bix->index >= removed_block) {
                                --bix->index;
                            }
                        }
                    }
                }
            }
        }

        return {new_blocks, removed_block};
    }

    template <typename Engine>
    Instruction simplify_non_terminator(
        Engine &engine, NonTerminator const &nt)
    {
        // Simplify the following instructions:
        //  - Dup{N}: Replace with Dup{N-1}
        //  - Swap{N}: Replace with Swap{N-1}
        //  - Instructions that push a value by reading some external state
        if (nt.opcode >= DUP2 && nt.opcode <= DUP16) {
            return NonTerminator{static_cast<uint8_t>(nt.opcode - 1), {}};
        }
        else if (nt.opcode >= SWAP2 && nt.opcode <= SWAP16) {
            return NonTerminator{static_cast<uint8_t>(nt.opcode - 1), {}};
        }
        else if (nt.opcode == CODESIZE) {
            return NonTerminator{static_cast<uint8_t>(CODESIZE), {}};
        } else if (nt.opcode == GASPRICE) {
            return random_constant(engine);
        }
        else {
            // Other non-terminators are not simplified
            return nt;
        }
    }

    template <typename Engine>
    Push simplify_push(Engine &engine, Push const &p)
    {
        return std::visit(
            Cases{
                [&](ValidAddress const &) -> Push {
                    return random_constant(engine);
                },
                [&](ValidJumpDest const &) -> Push {
                    return random_constant(engine);
                },
                [&](Constant const &c) -> Push {
                    // Half of the time, generate a smaller constant or divide
                    // the current value by 2.
                    if (toss(engine, 0.5)) {
                        auto const new_const = random_constant(engine);
                        return new_const.value < c.value ? new_const : c;
                    } else {
                        return Constant{c.value >> 1};
                    }
                },
            },
            p);
    }

    template <typename Engine>
    Instruction substitute_instruction(Engine &engine, Instruction const &instr)
    {
        // Simplify the following instructions:
        //  - Push: Shift the constant down to a small value
        //  - Dup{N}: Replace with Dup{N-1}
        //  - Swap{N}: Replace with Swap{N-1}
        //  - Instructions that read a value from memory, call data or the chain state
        return std::visit(
            Cases{
                [&](NonTerminator const &nt) -> Instruction {
                    return simplify_non_terminator(engine, nt);
                },
                [&](Push const &p) -> Instruction {
                    return simplify_push(engine, p);
                },
                [&instr](auto const &) -> Instruction { return instr; }
            },
            instr);
    }

    // To shrink a block, there are 2 strategies:
    // - remove ranges of instructions
    // - substitute instructions with simpler ones
    //
    // The substitution is particularly important, since dup and swap operations
    // force the stack to have a minimum height, which often prevents removing
    // other instructions. This problem manifests itself primarily when
    // shrinking a block with less than 32 instructions, since dup and swap
    // only operate on the first 32 stack elements.
    // To account for the following pattern:
    //  PUSH {Some important value}
    //  Push {Dummy value}
    //  Dup2 ; <- prevents removing the dummy value
    //
    // The substitution and removal strategies are interleaved a few times.
    template <typename Engine>
    std::vector<BasicBlock> shrink_block(
        Engine &engine, std::vector<BasicBlock> blocks,
        std::size_t block_to_shrink)
    {
        MONAD_VM_ASSERT(blocks.size() > block_to_shrink);
        auto block = blocks[block_to_shrink];
        MONAD_VM_ASSERT(block.instructions.size() != 0);
        block.instructions = erase_range(engine, std::move(block.instructions), 0.1);
        blocks[block_to_shrink] = block;
        return blocks;

        if (block.instructions.size() >= 40) {
            // 32 + some margin
            block.instructions = erase_range(engine, std::move(block.instructions), 0.1);
            blocks[block_to_shrink] = block;
            return blocks;
        } else {
            // Pick a number from 1 to 5
            auto const iterations = std::uniform_int_distribution<size_t>(1, 5)(engine);
            for (auto i = 0u; i < iterations && !block.instructions.empty(); ++i) {
                if (toss(engine, 0.2)) {
                    // Substitute an instruction
                    auto const instr_to_substitute =
                        std::uniform_int_distribution<size_t>(0, block.instructions.size() - 1)(engine);
                    std::cerr << std::format("substitute_instruction: {}\n", instr_to_substitute);
                    block.instructions[instr_to_substitute] = substitute_instruction(engine, block.instructions[instr_to_substitute]);
                } else {
                    std::cerr << std::format("erase_element\n");
                    block.instructions = erase_element(engine, std::move(block.instructions)).first;
                }
            }
            blocks[block_to_shrink] = block;
            return blocks;
        }
    }

    // Set the jumpdest flag of the basic block following jumpdest_block_ix
    std::pair<std::vector<BasicBlock>, bool> propagate_jumpdest(
        std::vector<BasicBlock> blocks, std::size_t jumpdest_block_ix)
    {
        bool propagated = false;
        if (jumpdest_block_ix < blocks.size()) {
            auto block = blocks[jumpdest_block_ix];
            propagated = !block.is_jump_dest;
            block.is_jump_dest = true;
            blocks[jumpdest_block_ix] = block;
        }

        return {blocks, propagated};
    }
}
