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
#include <limits>
#include <memory>
#include <random>
#include <unordered_set>
#include <variant>
#include <vector>
#include <iostream>

using namespace evmc::literals;

namespace monad::vm::fuzzing
{
    template <typename Engine>
    std::pair<std::vector<BasicBlock>, std::size_t> shrink_contract(Engine &engine, std::vector<BasicBlock> &blocks) {
        MONAD_VM_ASSERT(blocks.size() != 0);

        auto const block_to_remove =
            std::uniform_int_distribution<size_t>(
                0, static_cast<size_t>(blocks.size()) - 1)(engine);

        auto new_contract = blocks;
        new_contract.erase(new_contract.begin() + static_cast<ptrdiff_t>(block_to_remove));
        // We need to adjust jump destinations so they still point to their
        // original targets. Push instructions with a ValidJumpDest operand must
        // be decremented if they point to a block after the removed one.
        for (auto &block : new_contract) {
            for (auto &instr : block.instructions) {
                if (auto *push = std::get_if<Push>(&instr)) {
                    if (auto *vjd = std::get_if<ValidJumpDest>(push)) {
                        if (auto *bix = std::get_if<BlockIx>(vjd)) {
                            if (bix->index != 0 && bix->index >= block_to_remove) {
                                --bix->index;

                                if (!(bix->index < blocks.size())) {
                                    std::cerr << "After removing block " << block_to_remove << ", invalid jump dest " << bix->index << " in contract of size " << new_contract.size() << "\n";
                                }
                                MONAD_VM_ASSERT(bix->index < blocks.size());
                            }
                        }
                    }
                }
            }
        }

        return {new_contract, static_cast<std::size_t>(block_to_remove)};
    }

    template <typename Engine>
    std::pair<std::vector<BasicBlock>, std::size_t> shrink_block(Engine &engine, std::vector<BasicBlock> &blocks, std::size_t block_to_shrink) {
        MONAD_VM_ASSERT(blocks.size() != 0);
        auto block = blocks[block_to_shrink];
        MONAD_VM_ASSERT(block.instructions.size() != 0);

        using difference_type = ptrdiff_t;

        auto const instr_to_remove =
            std::uniform_int_distribution<difference_type>(
                0, static_cast<difference_type>(block.instructions.size()) - 1)(engine);

        std::cerr << "Shrinking block " << block_to_shrink << " with " << block.instructions.size() << " instructions. Picked instruction " << instr_to_remove << "\n";

        // Remove instruction
        block.instructions.erase(block.instructions.begin() + instr_to_remove);

        auto new_blocks = blocks;
        new_blocks[block_to_shrink] = block;
        return {new_blocks, instr_to_remove};
    }
}
