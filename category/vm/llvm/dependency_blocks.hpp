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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/evm/traits.hpp>

#include <iostream>
#include <optional>

using namespace monad::vm::compiler::basic_blocks;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler;
using enum OpCode;
using enum Terminator;

inline bool is_pure(OpCode op)
{
    return (
        op == Shl || op == Shr || op == Sar || op == Add || op == Mul ||
        op == Sub || op == Div || op == SDiv || op == Mod || op == SMod ||
        op == AddMod || op == MulMod || op == SignExtend || op == Lt ||
        op == Gt || op == SLt || op == SGt || op == Eq || op == IsZero ||
        op == And || op == Or || op == XOr || op == Not || op == Byte);

    // should just put true or false in the OpCodeInfo table in opcodes.hpp
}

namespace monad::vm::dependency_blocks
{

    typedef int32_t StackIdx;
    typedef size_t InstrIdx;

    typedef std::variant<uint256_t, InstrIdx> EvmValue;

    struct UnspillInstr
    {
        StackIdx idx;
    };

    struct SpillInstr
    {
        EvmValue val;
        StackIdx idx;
    };

    struct EvmInstr
    {
        Instruction instr;
        std::vector<EvmValue> args;
        int64_t remaining_block_base_gas;
    };

    typedef std::variant<
        struct EvmInstr, struct UnspillInstr, struct SpillInstr>
        Instr;

    inline Instr unspill_instr(StackIdx idx)
    {
        struct UnspillInstr e{idx};
        return e;
    };

    inline Instr spill_instr(EvmValue val, StackIdx idx)
    {
        struct SpillInstr e{val, idx};
        return e;
    };

    inline Instr evm_instr(
        Instruction instr, std::vector<EvmValue> args,
        int64_t remaining_block_base_gas)
    {
        struct EvmInstr e{instr, args, remaining_block_base_gas};
        return e;
    };

    struct DependencyBlock
    {
        InstrIdx insert_instr(
            Instr instr, std::vector<Instr> &blk_instrs,
            std::vector<bool> &blk_instrs_evaluated)
        {
            InstrIdx const idx = blk_instrs.size();
            blk_instrs.push_back(instr);
            blk_instrs_evaluated.push_back(false);
            return idx;
        }

        void expand_value_stack(
            int32_t low, std::vector<EvmValue> &value_stack,
            std::vector<Instr> &blk_instrs,
            std::vector<bool> &blk_instrs_evaluated)
        {
            for (int32_t i = -1; i >= low; --i) {

                InstrIdx idx = insert_instr(
                    unspill_instr(i), blk_instrs, blk_instrs_evaluated);
                value_stack.insert(value_stack.begin(), idx);
                // insert at the beginning so that it is easy to know the index
                // of unspills e.g., $0 = unspill -1, $1 = unspill -2 and so on
            }
        }

        std::vector<EvmValue>
        pop_args(uint8_t n, std::vector<EvmValue> &value_stack)
        {
            MONAD_VM_ASSERT(value_stack.size() >= n);

            std::vector<EvmValue> args;

            while (n > 0) {

                args.push_back(value_stack.back());
                value_stack.pop_back();
                n--;
            }

            return args;
        }

        bool is_evaluated(InstrIdx i, std::vector<bool> &blk_instrs_evaluated)
        {
            return blk_instrs_evaluated[i];
        }

        void evaluate(
            InstrIdx i, std::vector<Instr> &blk_instrs,
            std::vector<bool> &blk_instrs_evaluated)
        {
            blk_instrs_evaluated[i] = true;
            Instr instr = blk_instrs[i];
            std::visit<void>(
                Cases{
                    [&](struct EvmInstr &ei) {
                        uint8_t const n_args = ei.instr.stack_args();
                        ei.args.resize(n_args); // remove extra dependency added
                                                // to impure statements
                    },
                    [&](struct UnspillInstr &) {},
                    [&](struct SpillInstr &) {},
                },
                instr);

            instrs.emplace_back(i, instr);
        }

        void push_if_unevaluated(
            std::vector<InstrIdx> &deps, EvmValue v,
            std::vector<bool> &blk_instrs_evaluated)
        {
            std::visit<void>(
                Cases{
                    [&](uint256_t const &) {},
                    [&](InstrIdx const &i) {
                        if (!is_evaluated(i, blk_instrs_evaluated)) {
                            deps.push_back(i);
                        }
                    },
                },
                v);
        }

        InstrIdx unspill_offset_of(StackIdx i)
        {
            return (static_cast<InstrIdx>(-i - 1));
        }

        std::vector<InstrIdx> unevaluated_deps_of(
            InstrIdx i, std::vector<Instr> &blk_instrs,
            std::vector<bool> &blk_instrs_evaluated)
        {
            std::vector<InstrIdx> deps;

            std::visit<void>(
                Cases{
                    [&](struct EvmInstr const &ei) {
                        for (auto const arg : ei.args) {
                            push_if_unevaluated(
                                deps, arg, blk_instrs_evaluated);
                        }
                    },
                    [&](struct UnspillInstr const &) {},
                    [&](struct SpillInstr const &si) {
                        if (si.idx < 0) // this index is shared with an unspill
                        {
                            push_if_unevaluated(
                                deps,
                                unspill_offset_of(si.idx),
                                blk_instrs_evaluated);
                        }
                        push_if_unevaluated(deps, si.val, blk_instrs_evaluated);
                    },
                },
                blk_instrs[i]);

            return deps;
        }

        bool is_spill_terminator(Terminator t)
        {
            return (t == JumpI || t == Jump || t == FallThrough);
        }

    public:
        byte_offset offset;
        int64_t block_gas_update;

        int32_t low;
        int32_t high;
        int32_t delta;

        std::vector<std::tuple<InstrIdx, Instr>> instrs;

        Terminator terminator;
        block_id fallthrough_dest;
        std::vector<EvmValue> terminator_args;

    public:
        DependencyBlock(
            Block const &blk, int64_t blk_base_gas, int64_t blk_gas_update)
            : offset(blk.offset)
            , block_gas_update(blk_gas_update)
            , terminator(blk.terminator)
            , fallthrough_dest(blk.fallthrough_dest)
        {
            auto [low_, delta_, high_] = blk.stack_deltas();
            low = low_;
            delta = delta_;
            high = high_;

            int64_t remaining_block_base_gas = blk_base_gas;
            MONAD_VM_DEBUG_ASSERT(remaining_block_base_gas >= 0);

            std::optional<InstrIdx> last_stmt = std::nullopt;
            std::vector<InstrIdx> dependencies;

            std::vector<EvmValue> value_stack;
            std::vector<Instr> blk_instrs;
            std::vector<bool> blk_instrs_evaluated;

            expand_value_stack(
                low, value_stack, blk_instrs, blk_instrs_evaluated);

            for (auto const &instr : blk.instrs) {

                remaining_block_base_gas -= instr.static_gas_cost();

                uint8_t const n_args = instr.stack_args();
                auto const op = instr.opcode();

                switch (op) {

                case Pc:
                    value_stack.push_back(static_cast<uint256_t>(instr.pc()));
                    break;

                case Push:
                    value_stack.push_back(instr.immediate_value());
                    break;
                case Swap: {
                    uint8_t const i = instr.index();
                    std::swap(
                        value_stack.back(),
                        value_stack[value_stack.size() - i - 1]);
                } break;
                case Dup: {
                    uint8_t const i = instr.index();
                    value_stack.push_back(value_stack[value_stack.size() - i]);
                } break;
                case Pop:
                    value_stack.pop_back();
                    break;
                default:
                    std::vector<EvmValue> args = pop_args(n_args, value_stack);

                    if (!is_pure(op) && last_stmt.has_value()) {
                        // For impure operations add a dependency to the
                        // previous statement.  This (implicit) dependency is
                        // entirely used to preserve execution order and not
                        // used after that for code generation.
                        args.push_back(last_stmt.value());
                    }

                    InstrIdx idx = insert_instr(
                        evm_instr(instr, args, remaining_block_base_gas),
                        blk_instrs,
                        blk_instrs_evaluated);

                    if (!is_pure(op)) {
                        last_stmt = idx;
                    }

                    if (instr.increases_stack()) {
                        value_stack.push_back(idx);
                    }

                    break;
                };
            }

            uint8_t const term_n_args =
                static_cast<uint8_t>(terminator_inputs(blk.terminator));

            terminator_args = pop_args(term_n_args, value_stack);

            // push terminator dependencies first so they are processed last
            for (EvmValue const &val : terminator_args) {

                std::visit<void>(
                    Cases{
                        [&](uint256_t const &) {},
                        [&](InstrIdx const &i) { dependencies.push_back(i); },
                    },
                    val);
            };

            // dependencies needed for the statements
            if (last_stmt.has_value()) {
                dependencies.push_back(last_stmt.value());
            }

            // push spill dependencies last so they are processed first
            if (is_spill_terminator(blk.terminator)) {
                // spill dependencies
                StackIdx i = delta - static_cast<StackIdx>(value_stack.size());
                for (auto const &val : value_stack) {
                    dependencies.push_back(insert_instr(
                        spill_instr(val, i), blk_instrs, blk_instrs_evaluated));
                    ++i;
                }
            }

            while (!dependencies.empty()) {

                auto const v = dependencies.back();

                if (is_evaluated(v, blk_instrs_evaluated)) {
                    dependencies.pop_back();
                    continue;
                }

                std::vector<InstrIdx> needed_deps =
                    unevaluated_deps_of(v, blk_instrs, blk_instrs_evaluated);

                if (needed_deps.empty()) {
                    evaluate(v, blk_instrs, blk_instrs_evaluated);
                    continue;
                }

                dependencies.insert(
                    dependencies.end(), needed_deps.begin(), needed_deps.end());
            }
        };
    };

    class DependencyBlocksIR
    {
    private:
    public:
        std::unordered_map<byte_offset, block_id> jump_dests;
        std::vector<DependencyBlock> blocks;

        explicit DependencyBlocksIR(BasicBlocksIR const &ir)
            : jump_dests(ir.jump_dests())
        {
        }

        bool is_jumpdest(byte_offset offset)
        {
            auto const item = jump_dests.find(offset);
            return (item != jump_dests.end());
        };
    };

    inline void inline_empty_fallthroughs(DependencyBlocksIR &ir)
    {
        // rewrite from the bottom up so we can take advantage of previous
        // rewrites
        uint64_t i = ir.blocks.size();
        while (i > 0) {
            --i;
            DependencyBlock &blk = ir.blocks[i];
            if (blk.terminator == Terminator::FallThrough) {
                DependencyBlock const &dest = ir.blocks[blk.fallthrough_dest];
                if (dest.instrs.empty()) {
                    blk.block_gas_update += dest.block_gas_update;
                    blk.low = std::min(blk.low, blk.delta + dest.low);
                    blk.high = std::max(blk.high, blk.delta + dest.high);
                    blk.delta += dest.delta;
                    for (auto &[_, instr] : blk.instrs) {
                        std::visit<void>(
                            Cases{
                                [&](struct EvmInstr &ei) {
                                    ei.remaining_block_base_gas +=
                                        dest.block_gas_update;
                                },
                                [&](struct UnspillInstr const &) {},
                                [&](struct SpillInstr const &) {},
                            },
                            instr);
                    }
                    blk.terminator = dest.terminator;
                    blk.fallthrough_dest = dest.fallthrough_dest;
                    blk.terminator_args = dest.terminator_args;
                }
            }
        }
    };

    template <Traits traits>
    DependencyBlocksIR make_DependencyBlocksIR(BasicBlocksIR const &ir)
    {
        DependencyBlocksIR dep_ir(ir);
        for (auto const &blk : ir.blocks()) {
            int64_t const blk_base_gas = block_base_gas<traits>(blk);
            int64_t const blk_gas_update = dep_ir.is_jumpdest(blk.offset)
                                               ? 1 + blk_base_gas
                                               : blk_base_gas;

            dep_ir.blocks.emplace_back(blk, blk_base_gas, blk_gas_update);
        }
        inline_empty_fallthroughs(dep_ir);
        return dep_ir;
    }

};

/*
 * Formatter Implementations
 */

template <>
struct std::formatter<monad::vm::dependency_blocks::EvmValue>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::dependency_blocks::EvmValue const &v,
        std::format_context &ctx) const
    {
        using namespace monad::vm::dependency_blocks;
        using monad::vm::Cases;

        std::visit<void>(
            Cases{
                [&](uint256_t const &c) {
                    std::format_to(ctx.out(), "#{}", c);
                },
                [&](InstrIdx const &i) { std::format_to(ctx.out(), "${}", i); },
            },
            v);
        return ctx.out();
    }
};

template <>
struct std::formatter<monad::vm::dependency_blocks::Instr>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::dependency_blocks::Instr const &d,
        std::format_context &ctx) const
    {
        using namespace monad::vm::dependency_blocks;
        using monad::vm::Cases;

        std::visit<void>(
            Cases{
                [&](struct EvmInstr const &ei) {
                    std::format_to(ctx.out(), "{}", ei.instr);

                    for (auto const &arg : ei.args) {
                        std::format_to(ctx.out(), " {}", arg);
                    }

                    std::format_to(
                        ctx.out(), "  rbbg:{}", ei.remaining_block_base_gas);
                },
                [&](struct UnspillInstr const &ui) {
                    return std::format_to(ctx.out(), "unspill {}", ui.idx);
                },
                [&](struct SpillInstr const &si) {
                    return std::format_to(
                        ctx.out(), "spill {} {}", si.val, si.idx);
                },
            },
            d);
        return ctx.out();
    }
};

template <>
struct std::formatter<monad::vm::dependency_blocks::DependencyBlock>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::dependency_blocks::DependencyBlock const &blk,
        std::format_context &ctx) const
    {
        using namespace monad::vm::dependency_blocks;
        using monad::vm::Cases;

        std::format_to(ctx.out(), "  0x{:02x}:\n", blk.offset);

        for (auto const &[i, di] : blk.instrs) {
            std::format_to(ctx.out(), "      ");

            std::visit<void>(
                Cases{
                    [&](struct EvmInstr const &ei) {
                        if (ei.instr.increases_stack()) {
                            std::format_to(ctx.out(), "${} = ", i);
                        }
                    },
                    [&](struct UnspillInstr const &) {
                        std::format_to(ctx.out(), "${} = ", i);
                    },
                    [&](struct SpillInstr const &) {},
                },
                di);

            std::format_to(ctx.out(), "{}\n", di);
        }

        std::format_to(ctx.out(), "    {}", blk.terminator);
        if (blk.fallthrough_dest != monad::vm::compiler::INVALID_BLOCK_ID) {
            std::format_to(ctx.out(), " {}", blk.fallthrough_dest);
        }

        for (auto const &arg : blk.terminator_args) {
            std::format_to(ctx.out(), " {}", arg);
        }

        return std::format_to(ctx.out(), "\n");
    }
};

template <>
struct std::formatter<monad::vm::dependency_blocks::DependencyBlocksIR>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::dependency_blocks::DependencyBlocksIR const &ir,
        std::format_context &ctx) const
    {

        std::format_to(ctx.out(), "dependency_blocks:\n");
        int i = 0;
        for (auto const &blk : ir.blocks) {
            std::format_to(ctx.out(), "  block {}", i);
            std::format_to(ctx.out(), "{}", blk);
            i++;
        }
        std::format_to(ctx.out(), "\n  jumpdests:\n");
        for (auto const &[k, v] : ir.jump_dests) {
            std::format_to(ctx.out(), "    {}:{}\n", k, v);
        }
        return ctx.out();
    }
};
