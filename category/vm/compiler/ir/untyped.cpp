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
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed.hpp>
#include <category/vm/compiler/ir/poly_typed/block.hpp>
#include <category/vm/compiler/ir/poly_typed/kind.hpp>
#include <category/vm/compiler/ir/untyped.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>

#include <cstddef>
#include <format>
#include <limits>
#include <optional>
#include <span>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

using namespace monad::vm::compiler;

using monad::vm::Cases;

namespace monad::vm::compiler::untyped
{
    UntypedIR::UntypedIR(poly_typed::PolyTypedIR &&ir)
        : codesize{ir.codesize}
        , jumpdests{std::move(ir.jumpdests)}
        , blocks{build_untyped(jumpdests, std::move(ir.blocks))}
    {
    }

    struct Ignored
    {
    };

    std::variant<Addr, Word, Ignored> expected_jumpdest_type(
        std::vector<poly_typed::Kind> const &dest_block_kind,
        std::vector<poly_typed::Kind> const &output_stack_kind, size_t i)
    {
        if (i >= output_stack_kind.size()) {
            return Ignored{};
        }
        if (std::holds_alternative<poly_typed::Cont>(*output_stack_kind[i])) {
            if (i < dest_block_kind.size()) {
                MONAD_VM_ASSERT(
                    std::holds_alternative<poly_typed::Cont>(
                        *dest_block_kind[i]) ||
                    std::holds_alternative<poly_typed::KindVar>(
                        *dest_block_kind[i]));
            }
            return Addr{};
        }
        else if (std::holds_alternative<poly_typed::WordCont>(
                     *output_stack_kind[i])) {
            if (i < dest_block_kind.size() &&
                std::holds_alternative<poly_typed::Cont>(*dest_block_kind[i])) {
                return Addr{};
            }
            else {
                return Word{};
            }
        }
        else {
            if (i < dest_block_kind.size()) {
                MONAD_VM_ASSERT(!std::holds_alternative<poly_typed::Cont>(
                    *dest_block_kind[i]));
                MONAD_VM_ASSERT(!std::holds_alternative<poly_typed::WordCont>(
                    *dest_block_kind[i]));
            }

            return Ignored{};
        }
    }

    std::vector<poly_typed::Value> pad_output_stack(
        std::vector<poly_typed::Kind> const &output_stack_kind,
        std::span<poly_typed::Value> output_stack, size_t min_params)
    {
        auto stack = std::vector<poly_typed::Value>(
            output_stack.begin(), output_stack.end());
        // We need to pad out the output stack in case the inferred output type
        // refers to output stack items past the min_params number actually used
        // by the block.
        if (output_stack.size() < output_stack_kind.size()) {
            for (size_t i = 0, param = min_params;
                 i < output_stack_kind.size() - output_stack.size();
                 ++i, ++param) {
                stack.emplace_back(poly_typed::ValueIs::PARAM_ID, param);
            }
        }
        return stack;
    }

    std::variant<Addr, Word> current_type(
        std::vector<poly_typed::Kind> const &input_stack_kind,
        std::vector<poly_typed::Value> const &output_stack, size_t i)
    {
        switch (output_stack[i].is) {
        case poly_typed::ValueIs::LITERAL:
            return Word{};
        case poly_typed::ValueIs::PARAM_ID: {
            MONAD_VM_ASSERT(output_stack[i].param < input_stack_kind.size());
            poly_typed::Kind const &kind =
                input_stack_kind[output_stack[i].param];

            if (std::holds_alternative<poly_typed::Cont>(*kind)) {
                return Addr{};
            }
            else {
                return Word{};
            }
        }
        default:
            return Word{};
        }
    }

    std::vector<size_t> collect_coercions(
        std::vector<poly_typed::Kind> const &input_stack_kind,
        std::vector<poly_typed::Kind> const &dest_block_kind,
        std::vector<poly_typed::Kind> const &output_stack_kind,
        std::vector<poly_typed::Value> const &output_stack)
    {
        std::vector<size_t> coersions;
        for (size_t i = 0; i < output_stack_kind.size(); i++) {
            auto const current =
                current_type(input_stack_kind, output_stack, i);
            auto const expected =
                expected_jumpdest_type(dest_block_kind, output_stack_kind, i);
            if (!std::holds_alternative<Ignored>(expected)) {
                if (std::holds_alternative<Word>(current) &&
                    std::holds_alternative<Addr>(expected)) {
                    coersions.push_back(i);
                }
                else if (
                    std::holds_alternative<Addr>(current) &&
                    std::holds_alternative<Word>(expected)) {
                    MONAD_VM_ASSERT(false);
                }
                // current == Addr, jumpdest_type_may == Addr - nothing to do
                // current == Word, jumpdest_type_may == Word - nothing to do
            }
        }
        return coersions;
    }

    std::variant<std::vector<Block>, std::vector<local_stacks::Block>>
    build_untyped(
        std::unordered_map<byte_offset, block_id> const &jumpdests,
        std::vector<poly_typed::Block> &&typed_blocks)
    {
        auto const &pre_cont = typed_blocks.front().kind;
        if (!(pre_cont->front.size() == 0 &&
              std::holds_alternative<poly_typed::ContVar>(pre_cont->tail))) {
            std::vector<local_stacks::Block> untyped_blocks;
            untyped_blocks.reserve(typed_blocks.size());
            for (auto &tb : typed_blocks) {
                block_id fallthrough_dest = INVALID_BLOCK_ID;
                basic_blocks::Terminator terminator;
                std::visit<void>(
                    Cases{
                        [&](poly_typed::JumpI const &t) {
                            terminator = basic_blocks::Terminator::JumpI;
                            fallthrough_dest = t.fallthrough_dest;
                        },
                        [&](poly_typed::Jump const &) {
                            terminator = basic_blocks::Terminator::Jump;
                        },
                        [&](poly_typed::FallThrough const &t) {
                            terminator = basic_blocks::Terminator::FallThrough;
                            fallthrough_dest = t.fallthrough_dest;
                        },
                        [&](poly_typed::Return const &) {
                            terminator = basic_blocks::Terminator::Return;
                        },
                        [&](poly_typed::Revert const &) {
                            terminator = basic_blocks::Terminator::Revert;
                        },
                        [&](poly_typed::SelfDestruct const &) {
                            terminator = basic_blocks::Terminator::SelfDestruct;
                        },
                        [&](poly_typed::Stop const &) {
                            terminator = basic_blocks::Terminator::Stop;
                        },
                        [&](poly_typed::InvalidInstruction const &) {
                            terminator =
                                basic_blocks::Terminator::InvalidInstruction;
                        },
                    },
                    tb.terminator);

                untyped_blocks.push_back(
                    {tb.min_params,
                     std::move(tb.output),
                     std::move(tb.instrs),
                     terminator,
                     fallthrough_dest,
                     tb.offset});
            }
            return untyped_blocks;
        }

        std::vector<Block> blocks;
        blocks.reserve(typed_blocks.size());

        for (auto &tb : typed_blocks) {
            if (std::holds_alternative<poly_typed::ContWords>(tb.kind->tail)) {
                // If the inferred kind is Word... -> Exit
                // this block cannot be reachable from the entry-point
                // and can thus be marked as dead code
                blocks.push_back({tb.offset, tb.min_params, {}, DeadCode{}});
                continue;
            }

            Terminator t;
            if (std::holds_alternative<poly_typed::Return>(tb.terminator)) {
                t = Terminator{std::get<poly_typed::Return>(tb.terminator)};
            }
            else if (std::holds_alternative<poly_typed::Stop>(tb.terminator)) {
                t = Terminator{std::get<poly_typed::Stop>(tb.terminator)};
            }
            else if (std::holds_alternative<poly_typed::Revert>(
                         tb.terminator)) {
                t = Terminator{std::get<poly_typed::Revert>(tb.terminator)};
            }
            else if (std::holds_alternative<poly_typed::SelfDestruct>(
                         tb.terminator)) {
                t = Terminator{
                    std::get<poly_typed::SelfDestruct>(tb.terminator)};
            }
            else if (std::holds_alternative<poly_typed::InvalidInstruction>(
                         tb.terminator)) {
                t = Terminator{
                    std::get<poly_typed::InvalidInstruction>(tb.terminator)};
            }
            else if (std::holds_alternative<poly_typed::FallThrough>(
                         tb.terminator)) {
                poly_typed::FallThrough const &fallthrough =
                    std::get<poly_typed::FallThrough>(tb.terminator);

                auto const padded_output_stack = pad_output_stack(
                    fallthrough.fallthrough_kind->front,
                    tb.output,
                    tb.min_params);

                auto const coerce_to_addr = collect_coercions(
                    tb.kind->front,
                    typed_blocks[fallthrough.fallthrough_dest].kind->front,
                    fallthrough.fallthrough_kind->front,
                    padded_output_stack);

                t = FallThrough{coerce_to_addr, fallthrough.fallthrough_dest};
            }
            else {
                MONAD_VM_ASSERT(tb.output.size() > 0);
                auto const &jump_dest_value = tb.output.front();
                std::optional<poly_typed::ContKind> jump_dest_kind;
                JumpDest jump_dest;

                switch (jump_dest_value.is) {
                case poly_typed::ValueIs::COMPUTED: {
                    MONAD_VM_ASSERT(false);
                }
                case poly_typed::ValueIs::PARAM_ID: {
                    MONAD_VM_ASSERT(
                        jump_dest_value.param < tb.kind->front.size());
                    poly_typed::Kind const &kind =
                        tb.kind->front[jump_dest_value.param];
                    if (std::holds_alternative<poly_typed::Cont>(*kind)) {
                        jump_dest_kind = std::get<poly_typed::Cont>(*kind).cont;
                        jump_dest = Addr{};
                    }
                    else if (std::holds_alternative<poly_typed::WordCont>(
                                 *kind)) {
                        jump_dest_kind =
                            std::get<poly_typed::WordCont>(*kind).cont;
                        jump_dest = Word{};
                    }
                    else {
                        // If the block kind is not Word... -> Exit
                        // then the jump dest can only be a Cont or a
                        // WordCont
                        MONAD_VM_ASSERT(false);
                    }
                    break;
                }
                default: {
                    if (jump_dest_value.literal >
                        std::numeric_limits<size_t>::max()) {
                        jump_dest = Invalid{};
                        jump_dest_kind = std::nullopt;
                    }
                    else {
                        if (auto const block_offset_id = jumpdests.find(
                                static_cast<size_t>(jump_dest_value.literal));
                            block_offset_id != jumpdests.end()) {
                            jump_dest = block_offset_id->second;
                            MONAD_VM_ASSERT(
                                block_offset_id->second < typed_blocks.size());
                            jump_dest_kind =
                                typed_blocks[block_offset_id->second].kind;
                        }
                        else {
                            jump_dest = Invalid{};
                            jump_dest_kind = std::nullopt;
                        }
                    }
                }
                }

                if (std::holds_alternative<poly_typed::Jump>(tb.terminator)) {
                    poly_typed::Jump const &jump =
                        std::get<poly_typed::Jump>(tb.terminator);
                    std::span<poly_typed::Value> const output_tail(
                        tb.output.data() + 1, tb.output.size() - 1);
                    auto const padded_output_stack = pad_output_stack(
                        jump.jump_kind->front, output_tail, tb.min_params);
                    auto const coerce_to_addr =
                        jump_dest_kind ? collect_coercions(
                                             tb.kind->front,
                                             (*jump_dest_kind)->front,
                                             jump.jump_kind->front,
                                             padded_output_stack)
                                       : std::vector<size_t>{};

                    t = Jump{coerce_to_addr, jump_dest};
                }
                else {
                    poly_typed::JumpI const &jumpi =
                        std::get<poly_typed::JumpI>(tb.terminator);
                    std::span<poly_typed::Value> const output_tail(
                        tb.output.data() + 2, tb.output.size() - 2);
                    auto const padded_output_stack = pad_output_stack(
                        jumpi.jump_kind->front, output_tail, tb.min_params);
                    auto const coerce_to_addr =
                        jump_dest_kind ? collect_coercions(
                                             tb.kind->front,
                                             (*jump_dest_kind)->front,
                                             jumpi.jump_kind->front,
                                             padded_output_stack)
                                       : std::vector<size_t>{};
                    MONAD_VM_ASSERT(
                        jumpi.fallthrough_dest < typed_blocks.size());

                    auto const padded_output_stack_fallthrough =
                        pad_output_stack(
                            jumpi.fallthrough_kind->front,
                            output_tail,
                            tb.min_params);
                    auto const fallthrough_coerce_to_addr = collect_coercions(
                        tb.kind->front,
                        typed_blocks[jumpi.fallthrough_dest].kind->front,
                        jumpi.fallthrough_kind->front,
                        padded_output_stack_fallthrough);

                    t = JumpI{
                        coerce_to_addr,
                        jump_dest,
                        fallthrough_coerce_to_addr,
                        jumpi.fallthrough_dest};
                }
            }

            blocks.push_back(
                {tb.offset, tb.min_params, std::move(tb.instrs), t});
        }

        return blocks;
    }

}

std::format_context::iterator std::formatter<untyped::UntypedIR>::format(
    untyped::UntypedIR const &ir, std::format_context &ctx) const
{
    if (std::holds_alternative<std::vector<untyped::Block>>(ir.blocks)) {
        auto const &blocks = std::get<std::vector<untyped::Block>>(ir.blocks);
        for (auto const &b : blocks) {
            std::format_to(ctx.out(), "0x{:x}:\n", b.offset);
            if (ir.jumpdests.contains(b.offset)) {
                std::format_to(ctx.out(), "  JUMPDEST\n", b.offset);
            }
            for (auto const &ins : b.instrs) {
                std::format_to(ctx.out(), "  {}\n", ins);
            }
            std::format_to(ctx.out(), "\n");
            std::visit<void>(
                Cases{
                    [&](untyped::JumpI const &t) {
                        std::format_to(
                            ctx.out(),
                            "  JUMPI {} BLOCK_{}\n",
                            t.jump_dest,
                            t.fallthrough_dest);
                        std::format_to(ctx.out(), "  coerce to addr if:");
                        for (auto const &v : t.coerce_to_addr) {
                            std::format_to(ctx.out(), " {}", v);
                        }
                        std::format_to(ctx.out(), "\n  coerce to addr else :");
                        for (auto const &v : t.fallthrough_coerce_to_addr) {
                            std::format_to(ctx.out(), " {}", v);
                        }
                        std::format_to(ctx.out(), "\n");
                    },
                    [&](untyped::Jump const &t) {
                        std::format_to(ctx.out(), "  JUMP {}\n", t.jump_dest);
                        std::format_to(ctx.out(), "  coerce to addr:");
                        for (auto const &v : t.coerce_to_addr) {
                            std::format_to(ctx.out(), " {}", v);
                        }
                        std::format_to(ctx.out(), "\n");
                    },
                    [&](untyped::FallThrough const &t) {
                        std::format_to(
                            ctx.out(),
                            "  FALLTHROUGH 0x{}\n",
                            t.fallthrough_dest);
                        std::format_to(ctx.out(), "  coerce to addr:");
                        for (auto const &v : t.fallthrough_coerce_to_addr) {
                            std::format_to(ctx.out(), " {}", v);
                        }
                        std::format_to(ctx.out(), "\n");
                    },
                    [&](poly_typed::Return const &) {
                        std::format_to(ctx.out(), "  RETURN\n");
                    },
                    [&](poly_typed::Revert const &) {
                        std::format_to(ctx.out(), "  REVERT\n");
                    },
                    [&](poly_typed::SelfDestruct const &) {
                        std::format_to(ctx.out(), "  SELFDESTRUCT\n");
                    },
                    [&](poly_typed::Stop const &) {
                        std::format_to(ctx.out(), "  STOP\n");
                    },
                    [&](poly_typed::InvalidInstruction const &) {
                        std::format_to(ctx.out(), "  INVALIDINSTRUCTION\n");
                    },
                    [&](untyped::DeadCode const &) {
                        std::format_to(ctx.out(), "  DEAD CODE\n");
                    },
                },
                b.terminator);
        }
    }
    else {
        std::format_to(ctx.out(), "Invalid type\n");
    }

    return ctx.out();
}
