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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86/emitter.hpp>

#include <nlohmann/json.hpp>

using namespace monad::vm;

namespace
{
    using OperandLocations = compiler::native::OperandLocations;

    struct InstructionMetadata
    {
        Instruction instruction;
        std::vector<OperandLocations> operand_locations;
        std::vector<OperandLocations> result_locations;
    };

    struct OperandsLoggerState
    {
        // Reference to the original IR so we can map instructions back to their
        // original locations.
        // basic_blocks::BasicBlocksIR const &ir;
        // Metadata accumulated as the instructions are compiled.
        std::vector<std::vector<InstructionMetadata>> blocks_metadata;

        OperandsLoggerState(size_t blocks_count)
            : blocks_metadata(blocks_count)
        {
        }

        // Output JSON format
        //
        // type Obj = [Block]
        //
        // type Block = {
        //   instructions: [Instruction]
        //   offset: number,
        //   terminator: "JumpI" | "Return" | "Revert" | "Jump" | "SelfDestruct"
        //                       | "Stop" | "FallThrough" | "InvalidInstruction"
        //   fallthrough_dest: number?
        // }
        //
        // type OpCode = uint8
        //
        // type Instruction = {
        //   opcode: OpCode,
        //   immediate?: string,  // For push instructions
        //   index?: number,      // For push, swap, dup and log instructions
        //   opcode_name: string, // Name of the opcode
        //   operands: [Operand],
        //   outputs: [Operand]
        // }
        //
        // type Operand = {
        //   literal: string?,
        //   general_reg: number?,
        //   avx_reg: number?,
        //   stack_offset: number?,
        //   deferred_comparison: boolean?
        // }
        nlohmann::json to_json(std::vector<OperandLocations> locations)
        {
            auto obj = nlohmann::json::array();
            for (auto const &opnd : locations) {
                nlohmann::json opnd_json;
                if (opnd.literal) {
                    opnd_json["literal"] =
                        std::format("{}", opnd.literal->value);
                }
                if (opnd.general_reg) {
                    opnd_json["general_reg"] = opnd.general_reg->reg;
                }
                if (opnd.avx_reg) {
                    opnd_json["avx_reg"] = opnd.avx_reg->reg;
                }
                if (opnd.stack_offset) {
                    opnd_json["stack_offset"] = opnd.stack_offset->offset;
                }
                if (opnd.is_deferred_comparison) {
                    opnd_json["deferred_comparison"] = true;
                }
                obj.push_back(opnd_json);
            }
            return obj;
        }

        nlohmann::json to_json(basic_blocks::BasicBlocksIR const &ir)
        {
            auto blocks = ir.blocks();
            nlohmann::json object = nlohmann::json::array();

            for (size_t i = 0; i < blocks_metadata.size(); ++i) {
                auto const &block_metadata = blocks_metadata[i];
                nlohmann::json block_json;
                block_json["instructions"] = nlohmann::json::array();
                block_json["offset"] = blocks[i].offset;
                block_json["terminator"] =
                    std::format("{}", blocks[i].terminator);

                if (blocks[i].fallthrough_dest != INVALID_BLOCK_ID) {
                    block_json["fallthrough_dest"] = blocks[i].fallthrough_dest;
                }

                for (auto const &[instr, opnds, outputs] : block_metadata) {
                    nlohmann::json instr_json;
                    auto opcode = instr.opcode();
                    instr_json["opcode"] = opcode;
                    if (opcode == OpCode::Push) {
                        instr_json["immediate"] =
                            std::format("{}", instr.immediate_value());
                    }
                    if (opcode == OpCode::Push || opcode == OpCode::Swap ||
                        opcode == OpCode::Dup || opcode == OpCode::Log) {
                        instr_json["index"] = instr.index();
                    }
                    instr_json["opcode_name"] = opcode_name(opcode);
                    instr_json["operands"] = to_json(opnds);
                    instr_json["outputs"] = to_json(outputs);
                    block_json["instructions"].push_back(instr_json);
                }
                object.push_back(block_json);
            }
            return object;
        }
    };

    std::optional<std::vector<OperandLocations>>
    peek_stack(compiler::native::Emitter &emit, uint8_t length)
    {
        // Stack underflow check
        if (emit.get_stack().top_index() - emit.get_stack().bottom_index() <
            length) {
            return std::nullopt;
        }
        std::vector<OperandLocations> elems;
        elems.reserve(length);
        for (size_t i = 0; i < length; ++i) {
            elems.push_back(emit.get_stack().get_stack_elem_locations(
                emit.get_stack().top_index() - static_cast<int32_t>(i)));
        }
        return elems;
    }

    auto operands_logger_make_hooks(OperandsLoggerState &state)
    {
        auto pre_hook =
            [&state](auto &emitter, auto block_ix, auto instr_ix, auto &instr) {
                (void)instr_ix; // Avoid unused variable warning

                std::optional<std::vector<OperandLocations>> instr_args =
                    peek_stack(emitter, instr.stack_args());

                if (!instr_args) {
                    std::cerr << "Error: peek_stack returned nullopt. "
                                 "instr.stack_args() = "
                              << instr.stack_args()
                              << ", emit.get_stack().top_index() = "
                              << emitter.get_stack().top_index() << std::endl;
                }
                else {
                    state.blocks_metadata[block_ix].push_back(
                        InstructionMetadata{instr, instr_args.value(), {}});
                }
            };

        auto post_hook =
            [&state](auto &emitter, auto block_ix, auto instr_ix, auto &instr) {
                std::optional<std::vector<OperandLocations>> instr_results =
                    peek_stack(emitter, instr.stack_increase());

                if (!instr_results) {
                    std::cerr << "Error: peek_stack returned nullopt. "
                                 "instr.stack_increase() = "
                              << instr.stack_increase()
                              << ", emit.get_stack().top_index() = "
                              << emitter.get_stack().top_index() << std::endl;
                }
                else {
                    state.blocks_metadata[block_ix][instr_ix].result_locations =
                        instr_results.value();
                }
            };
        return std::tuple{pre_hook, post_hook};
    }
}
