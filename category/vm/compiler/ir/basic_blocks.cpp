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
#include <category/vm/compiler/types.hpp>

#include <algorithm>
#include <cstdint>
#include <tuple>
#include <unordered_map>
#include <vector>

namespace monad::vm::compiler::basic_blocks
{
    /*
     * Block
     */

    bool Block::is_valid() const
    {
        return is_fallthrough_terminator(terminator) ==
               (fallthrough_dest != INVALID_BLOCK_ID);
    }

    // returns a tuple of:
    // the minimum delta the stack will decrease
    // the overall delta of the stack
    // the maximum delta the stack will increase
    std::tuple<std::int32_t, std::int32_t, std::int32_t>
    Block::stack_deltas() const
    {
        std::int32_t min_delta = 0;
        std::int32_t delta = 0;
        std::int32_t max_delta = 0;

        for (auto const &instr : instrs) {
            delta -= instr.stack_args();
            min_delta = std::min(delta, min_delta);

            delta += instr.stack_increase();
            max_delta = std::max(delta, max_delta);
        }

        delta -= static_cast<std::int32_t>(
            basic_blocks::terminator_inputs(terminator));
        min_delta = std::min(delta, min_delta);

        return {min_delta, delta, max_delta};
    }

    bool operator==(Block const &a, Block const &b)
    {
        return std::tie(a.instrs, a.terminator, a.fallthrough_dest, a.offset) ==
               std::tie(b.instrs, b.terminator, b.fallthrough_dest, b.offset);
    }

    /*
     * IR
     */

    bool BasicBlocksIR::is_valid() const
    {
        auto const all_blocks_valid =
            std::all_of(blocks_.begin(), blocks_.end(), [](auto const &b) {
                return b.is_valid();
            });

        auto const all_dests_valid = std::all_of(
            jump_dests_.begin(), jump_dests_.end(), [this](auto const &entry) {
                auto [offset, block_id] = entry;
                return block_id < blocks_.size();
            });

        return all_blocks_valid && all_dests_valid;
    }

    /*
     * IR: Private construction methods
     */

    void BasicBlocksIR::add_block(byte_offset offset)
    {
        blocks_.push_back(Block{.offset = offset});
        blocks_.back().instrs.reserve(16);
    }

    void BasicBlocksIR::add_terminator(Terminator t)
    {
        blocks_.back().instrs.shrink_to_fit();
        blocks_.back().terminator = t;
    }

    void BasicBlocksIR::add_fallthrough_terminator(Terminator t)
    {
        add_terminator(t);
        blocks_.back().fallthrough_dest = curr_block_id() + 1;
    }
}
