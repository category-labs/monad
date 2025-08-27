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

#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/evm/chain.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>

#include <evmc/evmc.h>

#include <limits>
#include <unordered_map>
#include <utility>
#include <variant>

namespace monad::vm::compiler::basic_blocks
{
    /**
     * Represents the subset of EVM instructions that may terminate a basic
     * block.
     *
     * After executing one of these instructions, control may not transfer
     * linearly to the next instruction in the program. Instead, execution may
     * either jump to a new program counter, or terminate entirely by handing
     * control back to the VM host.
     *
     * Note that `FallThrough` does not directly correspond to an EVM opcode;
     * these terminators occur when a block ends with a `JUMPDEST` instruction.
     * Here, the `JUMPDEST` needs to occur at the beginning of the following
     * block for gas accounting, but the current block still needs to be
     * terminated.
     */
    enum class Terminator
    {
        FallThrough,
        JumpI,
        Jump,
        Return,
        Stop,
        Revert,
        SelfDestruct,
        InvalidInstruction,
    };

    struct JumpDest
    {
        std::uint32_t pc;
    };

    constexpr OpCode evm_op_to_opcode(std::uint8_t op)
    {
        using enum OpCode;

        if (is_push_opcode(op)) {
            return Push;
        }

        if (is_swap_opcode(op)) {
            return Swap;
        }

        if (is_dup_opcode(op)) {
            return Dup;
        }

        if (is_log_opcode(op)) {
            return Log;
        }

        return OpCode(op);
    }

    /**
     * Return true if this terminator can implicitly fall through to the next
     * block in sequence.
     */
    constexpr bool is_fallthrough_terminator(Terminator t)
    {
        return t == Terminator::FallThrough || t == Terminator::JumpI;
    }

    /**
     * Base gas usage for a given terminator.
     */
    template <Traits traits>
    constexpr std::uint16_t terminator_static_gas(Terminator t)
    {
        using enum Terminator;
        switch (t) {
        case JumpI:
            return 10;
        case Return:
            return 0;
        case Revert:
            return 0;
        case Jump:
            return 8;
        case SelfDestruct: {
            if constexpr (traits::evm_rev() < EVMC_TANGERINE_WHISTLE) {
                return 0;
            }
            else {
                return 5000;
            }
        }
        case Stop:
            return 0;
        case FallThrough:
            return 0;
        case InvalidInstruction:
            return 0;
        }

        std::unreachable();
    }

    /**
     * Return the number of input stack elements consumed by each block
     * terminator.
     */
    constexpr std::size_t terminator_inputs(Terminator t)
    {
        using enum Terminator;
        switch (t) {
        case JumpI:
        case Return:
        case Revert:
            return 2;
        case Jump:
        case SelfDestruct:
            return 1;
        case Stop:
        case FallThrough:
        case InvalidInstruction:
            return 0;
        }

        std::unreachable();
    }

    /**
     * A basic block is a linear sequence of EVM instructions ending with a
     * single terminator.
     */
    struct Block
    {
        /**
         * The linear sequence of instructions that make up this block.
         *
         * It is legal for the body of a block to be empty; every valid block is
         * terminated.
         */
        std::vector<Instruction> instrs = {};

        /**
         * The terminator that ends this block.
         */
        Terminator terminator = Terminator::Stop;

        /**
         * The block ID that control should fall through to at the end of this
         * block, if the terminator of the block is a `JUMPI` instruction or an
         * implicit fallthrough.
         */
        block_id fallthrough_dest = INVALID_BLOCK_ID;

        /**
         * The basic block byte code offset.
         */
        byte_offset offset = 0;

        /**
         * Returns true if this block is well-formed.
         *
         * A well-formed block satisfies the following conditions:
         * - None of the instructions in `instrs` is a terminator.
         * - The `fallthrough_dest` is valid iff the block is terminated by a
         *   `JUMPI` instruction or an implicit fallthrough.
         */
        bool is_valid() const;
        std::tuple<std::int32_t, std::int32_t, std::int32_t>
        stack_deltas() const;
    };

    bool operator==(Block const &a, Block const &b);

    template <Traits traits>
    struct ChainMarker
    {
    };

    /**
     * In this representation, the underlying EVM code has been grouped into
     * basic blocks by splitting the program at terminator points.
     *
     * Blocks are assigned integer identifiers based on the order in which they
     * appear in the original program, and a table of jump destinations is
     * constructed that maps byte offsets in the original program onto these
     * block identifiers.
     */
    class BasicBlocksIR
    {
    public:
        /**
         * Construct basic blocks from a bytecode program.
         */
        template <Traits traits = EvmChain<EVMC_LATEST_STABLE_REVISION>>
        BasicBlocksIR(
            std::uint8_t const *, interpreter::code_size_t,
            ChainMarker<traits> = {});

        template <Traits traits = EvmChain<EVMC_LATEST_STABLE_REVISION>>
        [[gnu::always_inline]]
        static constexpr BasicBlocksIR unsafe_from(
            std::initializer_list<std::uint8_t const> bytes,
            ChainMarker<traits> rm = {})
        {
            MONAD_VM_ASSERT(bytes.size() <= *interpreter::code_size_t::max());
            return BasicBlocksIR(
                std::data(bytes),
                interpreter::code_size_t::unsafe_from(
                    static_cast<uint32_t>(bytes.size())),
                rm);
        }

        template <Traits traits = EvmChain<EVMC_LATEST_STABLE_REVISION>>
        [[gnu::always_inline]]
        static constexpr BasicBlocksIR unsafe_from(
            std::span<std::uint8_t const> bytes, ChainMarker<traits> rm = {})
        {
            MONAD_VM_ASSERT(bytes.size() <= *interpreter::code_size_t::max());
            return BasicBlocksIR(
                bytes.data(),
                interpreter::code_size_t::unsafe_from(
                    static_cast<uint32_t>(bytes.size())),
                rm);
        }

        /**
         * The basic blocks in the program.
         *
         * Blocks have an implicit integer identifier based on the order in
         * which they appear in this vector.
         */
        std::vector<Block> const &blocks() const
        {
            return blocks_;
        }

        std::vector<Block> &blocks()
        {
            return blocks_;
        }

        /// Size of bytecode
        interpreter::code_size_t codesize;

        /**
         * Retrieve a block by its identifier.
         */
        Block const &block(block_id id) const
        {
            return blocks_.at(id);
        }

        /**
         * A table mapping byte offsets into the original EVM code onto block
         * identifiers.
         */
        std::unordered_map<byte_offset, block_id> const &jump_dests() const
        {
            return jump_dests_;
        }

        std::unordered_map<byte_offset, block_id> &jump_dests()
        {
            return jump_dests_;
        }

        /**
         * A program in this representation is valid if:
         * - Each block in the program is valid.
         * - Each entry in the jumpdest table maps to a valid block.
         */
        bool is_valid() const;

    private:
        template <Traits traits>
        static std::variant<Instruction, Terminator, JumpDest> scan_from(
            std::span<std::uint8_t const> bytes, std::uint32_t &current_offset);

        std::vector<Block> blocks_;
        std::unordered_map<byte_offset, block_id> jump_dests_;

        /**
         * During construction, the ID of the block currently being built.
         */
        block_id curr_block_id() const
        {
            return blocks_.size() - 1;
        }

        /**
         * During construction, the byte offset of the block currently being
         * built.
         */
        byte_offset curr_block_offset() const
        {
            return blocks_.back().offset;
        }

        /**
         * During construction, add a new entry to the jump destination table
         * when a `JUMPDEST` instruction is parsed.
         */
        void add_jump_dest()
        {
            MONAD_VM_DEBUG_ASSERT(blocks_.back().instrs.empty());
            jump_dests_.emplace(curr_block_offset(), curr_block_id());
        }

        /**
         * During construction, begin building a new block.
         */
        void add_block(byte_offset offset);

        /**
         * During construction, set the terminator for the block currently being
         * built.
         */
        void add_terminator(Terminator t);

        /**
         * During construction, set the terminator for the block currently being
         * built, and set the fallthrough destination ID to that of the next
         * block that will be built.
         */
        void add_fallthrough_terminator(Terminator t);
    };

    template <Traits traits, typename... Args>
    BasicBlocksIR make_ir(Args &&...);

    template <Traits traits, typename... Args>
    BasicBlocksIR unsafe_make_ir(Args &&...);

    template <Traits traits>
    std::variant<Instruction, Terminator, JumpDest> BasicBlocksIR::scan_from(
        std::span<std::uint8_t const> bytes, std::uint32_t &current_offset)
    {
        MONAD_VM_DEBUG_ASSERT(current_offset < bytes.size());

        auto opcode = bytes[current_offset];
        auto opcode_offset = current_offset;

        auto const &info = opcode_table<traits>[opcode];
        current_offset++;

        if (is_unknown_opcode_info<traits>(info)) {
            return Terminator::InvalidInstruction;
        }

        switch (opcode) {
        case JUMPI:
            return Terminator::JumpI;
        case JUMP:
            return Terminator::Jump;
        case RETURN:
            return Terminator::Return;
        case STOP:
            return Terminator::Stop;
        case REVERT:
            return Terminator::Revert;
        case SELFDESTRUCT:
            return Terminator::SelfDestruct;
        case JUMPDEST:
            return JumpDest{opcode_offset};
        default:
            break;
        }

        auto const imm_size = info.num_args;
        uint256_t imm_value{0};

        if (imm_size > 0) {
            imm_value = runtime::from_bytes(
                imm_size,
                bytes.size() - current_offset,
                bytes.data() + current_offset);

            current_offset += imm_size;
        }

        return Instruction(
            opcode_offset,
            evm_op_to_opcode(opcode),
            imm_value,
            info.min_gas,
            info.min_stack,
            info.index,
            info.stack_increase,
            info.dynamic_gas);
    }

    template <Traits traits>
    int32_t block_base_gas(Block const &block)
    {
        int32_t base_gas = 0;
        for (auto const &instr : block.instrs) {
            base_gas += instr.static_gas_cost();
        }
        auto term_gas =
            basic_blocks::terminator_static_gas<traits>(block.terminator);
        // This is also correct for fall through and invalid instruction:
        return base_gas + term_gas;
    }

    template <Traits traits>
    BasicBlocksIR::BasicBlocksIR(
        std::uint8_t const *bytes, interpreter::code_size_t byte_count,
        ChainMarker<traits>)
        : codesize(byte_count)
    {
        using monad::vm::Cases;

        enum class St
        {
            INSIDE_BLOCK,
            OUTSIDE_BLOCK
        };

        St st = St::INSIDE_BLOCK;

        add_block(0);

        auto current_offset = std::uint32_t{0};
        auto first = true;

        while (current_offset < *byte_count) {
            auto inst = scan_from<traits>({bytes, *byte_count}, current_offset);

            if (first && std::holds_alternative<JumpDest>(inst)) {
                add_jump_dest();
                first = false;
                continue;
            }

            if (st == St::OUTSIDE_BLOCK) {
                if (std::holds_alternative<JumpDest>(inst)) {
                    add_block(std::get<JumpDest>(inst).pc);
                    st = St::INSIDE_BLOCK;
                    add_jump_dest();
                }
            }
            else {
                MONAD_VM_ASSERT(st == St::INSIDE_BLOCK);

                auto handle_terminator = [&](Terminator t) {
                    using enum Terminator;
                    MONAD_VM_ASSERT(t != FallThrough);

                    if (t == JumpI) {
                        add_fallthrough_terminator(JumpI);
                        add_block(current_offset);
                        // a corner case where we fall through JUMPI
                        // into a block starting with JUMPDEST, in which
                        // case we don't want to immediately FallThrough
                        // again, but instead just advance tok and mark
                        // the block as being a jumpdest
                        if (current_offset < *byte_count) {
                            auto next_offset = current_offset;
                            auto next_inst = scan_from<traits>(
                                {bytes, *byte_count}, next_offset);
                            if (std::holds_alternative<JumpDest>(next_inst)) {
                                current_offset += 1;
                                add_jump_dest();
                            }
                        }
                        return;
                    }

                    add_terminator(t);
                    st = St::OUTSIDE_BLOCK;
                };

                std::visit(
                    Cases{
                        handle_terminator,

                        [&](Instruction const &i) {
                            blocks_.back().instrs.push_back(i);
                        },

                        [&](JumpDest jd) {
                            add_fallthrough_terminator(Terminator::FallThrough);
                            add_block(jd.pc);
                            add_jump_dest();
                        },
                    },
                    inst);
            }
            first = false;
        }
    }

    template <Traits traits, typename... Args>
    BasicBlocksIR make_ir(Args &&...args)
    {
        return BasicBlocksIR(
            std::forward<Args>(args)..., ChainMarker<traits>{});
    }

    template <Traits traits, typename... Args>
    BasicBlocksIR unsafe_make_ir(Args &&...args)
    {
        return BasicBlocksIR::unsafe_from(
            std::forward<Args>(args)..., ChainMarker<traits>{});
    }
}

/*
 * Formatter Implementations
 */

template <>
struct std::formatter<monad::vm::compiler::basic_blocks::Terminator>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::basic_blocks::Terminator const &t,
        std::format_context &ctx) const
    {
        auto const *v = [t] {
            using enum monad::vm::compiler::basic_blocks::Terminator;

            switch (t) {
            case FallThrough:
                return "FallThrough";
            case JumpI:
                return "JumpI";
            case Jump:
                return "Jump";
            case Return:
                return "Return";
            case Revert:
                return "Revert";
            case SelfDestruct:
                return "SelfDestruct";
            case Stop:
                return "Stop";
            case InvalidInstruction:
                return "InvalidInstruction";
            }

            std::unreachable();
        }();

        return std::format_to(ctx.out(), "{}", v);
    }
};

template <>
struct std::formatter<monad::vm::compiler::basic_blocks::Block>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::basic_blocks::Block const &blk,
        std::format_context &ctx) const
    {
        std::format_to(ctx.out(), "  0x{:02x}:\n", blk.offset);

        for (auto const &tok : blk.instrs) {
            std::format_to(ctx.out(), "      {}\n", tok);
        }

        std::format_to(ctx.out(), "    {}", blk.terminator);
        if (blk.fallthrough_dest != monad::vm::compiler::INVALID_BLOCK_ID) {
            std::format_to(ctx.out(), " {}", blk.fallthrough_dest);
        }
        return std::format_to(ctx.out(), "\n");
    }
};

template <>
struct std::formatter<monad::vm::compiler::basic_blocks::BasicBlocksIR>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::basic_blocks::BasicBlocksIR const &ir,
        std::format_context &ctx) const
    {

        std::format_to(ctx.out(), "basic_blocks:\n");
        int i = 0;
        for (auto const &blk : ir.blocks()) {
            std::format_to(ctx.out(), "  block {}", i);
            std::format_to(ctx.out(), "{}", blk);
            i++;
        }
        std::format_to(ctx.out(), "\n  jumpdests:\n");
        for (auto const &[k, v] : ir.jump_dests()) {
            std::format_to(ctx.out(), "    {}:{}\n", k, v);
        }
        return std::format_to(ctx.out(), "");
    }
};
