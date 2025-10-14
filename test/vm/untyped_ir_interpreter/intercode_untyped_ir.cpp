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

#include <category/vm/core/assert.h>
#include <category/vm/evm/opcodes.hpp>
#include <test/vm/untyped_ir_interpreter/intercode_untyped_ir.hpp>

#include <algorithm>
#include <cstdint>
#include <span>

using namespace monad::vm::compiler;

namespace monad::vm::interpreter
{

    IntercodeUntypedIR::IntercodeUntypedIR(
        std::span<std::uint8_t const> const code)
        : padded_code_(pad(code))
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code.size())))
        , jumpdest_map_(find_jumpdests(code))
        , ir(untyped::UntypedIR{
              poly_typed::PolyTypedIR{local_stacks::LocalStacksIR{
                  basic_blocks::BasicBlocksIR{code.data(), code_size_}}}})
        , fallthrough_coerce_map(build_fallthrough_coerce_map(ir))
        , jump_coerce_map(build_jump_coerce_map(ir))
        , jumpdest_addr(build_jumpdest_addr_set(ir))
    {
    }

    IntercodeUntypedIR::~IntercodeUntypedIR()
    {
        delete[] (padded_code_ - start_padding_size);
    }

    std::uint8_t const *
    IntercodeUntypedIR::pad(std::span<std::uint8_t const> const code)
    {
        MONAD_VM_ASSERT(code.size() <= *code_size_t::max());
        auto *buffer = new std::uint8_t
            [start_padding_size + code.size() + end_padding_size];

        std::fill_n(&buffer[0], start_padding_size, 0);
        std::copy(code.begin(), code.end(), &buffer[start_padding_size]);
        std::fill_n(
            &buffer[code.size() + start_padding_size], end_padding_size, 0);

        return buffer + start_padding_size;
    }

    std::unordered_map<std::size_t, std::vector<std::size_t>>
    IntercodeUntypedIR::build_fallthrough_coerce_map(
        monad::vm::compiler::untyped::UntypedIR ir)
    {
        std::unordered_map<std::size_t, std::vector<std::size_t>>
            fallthrough_coerce_map;
        if (!std::holds_alternative<std::vector<untyped::Block>>(ir.blocks)) {
            return fallthrough_coerce_map;
        }

        auto const &blocks = std::get<std::vector<untyped::Block>>(ir.blocks);

        for (auto it = blocks.begin(); it != blocks.end(); ++it) {
            auto const &b = *it;

            if (std::holds_alternative<untyped::FallThrough>(b.terminator) &&
                std::get<untyped::FallThrough>(b.terminator)
                    .fallthrough_coerce_to_addr.size()) {
                // if the block has a fallthrough terminator, that means the
                // next block must begin with a jumpdest, hence we store the
                // offset to the jumpdest instruction of the next block in the
                // map. when we fallthrough to a new block in the interpreter
                // (i.e. the is_fallthrough flag is set) we will check in the
                // fallthrough map to see if any coercions fromt he previous
                // block should be applied
                auto next_block_it = it + 1;
                if (next_block_it != blocks.end()) {
                    auto next_block_offset = next_block_it->offset;
                    fallthrough_coerce_map[next_block_offset] =
                        std::get<untyped::FallThrough>(b.terminator)
                            .fallthrough_coerce_to_addr;
                }
            }
            else if (
                std::holds_alternative<untyped::JumpI>(b.terminator) &&
                std::get<untyped::JumpI>(b.terminator)
                    .fallthrough_coerce_to_addr.size()) {
                auto last_instr_offset = ir.last_instruction_offset(b);
                fallthrough_coerce_map[last_instr_offset] =
                    std::get<untyped::JumpI>(b.terminator)
                        .fallthrough_coerce_to_addr;
            }
        }

        return fallthrough_coerce_map;
    }

    std::unordered_map<std::size_t, std::vector<std::size_t>>
    IntercodeUntypedIR::build_jump_coerce_map(
        monad::vm::compiler::untyped::UntypedIR ir)
    {
        std::unordered_map<std::size_t, std::vector<std::size_t>>
            jump_coerce_map;
        if (!std::holds_alternative<std::vector<untyped::Block>>(ir.blocks)) {
            return jump_coerce_map;
        }

        auto const &blocks = std::get<std::vector<untyped::Block>>(ir.blocks);

        for (auto const &b : blocks) {
            if (std::holds_alternative<untyped::Jump>(b.terminator) &&
                std::get<untyped::Jump>(b.terminator).coerce_to_addr.size()) {
                auto last_instr_offset = ir.last_instruction_offset(b);
                jump_coerce_map[last_instr_offset] =
                    std::get<untyped::Jump>(b.terminator).coerce_to_addr;
            }
            else if (
                std::holds_alternative<untyped::JumpI>(b.terminator) &&
                std::get<untyped::JumpI>(b.terminator).coerce_to_addr.size()) {
                auto last_instr_offset = ir.last_instruction_offset(b);
                jump_coerce_map[last_instr_offset] =
                    std::get<untyped::JumpI>(b.terminator).coerce_to_addr;
            }
        }

        return jump_coerce_map;
    }

    std::unordered_set<std::size_t> IntercodeUntypedIR::build_jumpdest_addr_set(
        monad::vm::compiler::untyped::UntypedIR ir)
    {
        std::unordered_set<std::size_t> jumpdest_addr;
        if (!std::holds_alternative<std::vector<untyped::Block>>(ir.blocks)) {
            return jumpdest_addr;
        }

        auto const &blocks = std::get<std::vector<untyped::Block>>(ir.blocks);

        for (auto const &b : blocks) {
            if (std::holds_alternative<untyped::Jump>(b.terminator)) {
                auto last_instr_offset = ir.last_instruction_offset(b);
                if (std::holds_alternative<untyped::Addr>(
                        std::get<untyped::Jump>(b.terminator).jump_dest)) {
                    jumpdest_addr.insert(last_instr_offset);
                }
            }
            else if (std::holds_alternative<untyped::JumpI>(b.terminator)) {
                auto last_instr_offset = ir.last_instruction_offset(b);
                if (std::holds_alternative<untyped::Addr>(
                        std::get<untyped::JumpI>(b.terminator).jump_dest)) {
                    jumpdest_addr.insert(last_instr_offset);
                }
            }
        }

        return jumpdest_addr;
    }

    auto
    IntercodeUntypedIR::find_jumpdests(std::span<std::uint8_t const> const code)
        -> JumpdestMap
    {
        auto jumpdests = JumpdestMap(code.size(), false);

        for (auto i = 0u; i < code.size(); ++i) {
            auto const op = code[i];

            if (op == EvmOpCode::JUMPDEST) {
                jumpdests[i] = true;
            }

            if (is_push_opcode(op)) {
                i += get_push_opcode_index(op);
            }
        }

        return jumpdests;
    }
}
