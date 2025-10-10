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
    std::vector<BasicBlock> shrink_block(
        Engine &engine, std::vector<BasicBlock> blocks,
        std::size_t block_to_shrink)
    {
        MONAD_VM_ASSERT(blocks.size() != 0);
        auto block = blocks[block_to_shrink];
        MONAD_VM_ASSERT(block.instructions.size() != 0);

        auto new_instructions =
            erase_range(engine, std::move(block.instructions), 0.1);
        block.instructions = new_instructions;
        blocks[block_to_shrink] = block;
        return blocks;
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
