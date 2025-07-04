#include <monad/vm/compiler/ir/instruction.hpp>
#include <monad/vm/compiler/ir/local_stacks.hpp>
#include <monad/vm/compiler/ir/poly_typed.hpp>
#include <monad/vm/compiler/ir/poly_typed/block.hpp>
#include <monad/vm/compiler/ir/poly_typed/infer.hpp>
#include <monad/vm/compiler/ir/poly_typed/kind.hpp>
#include <monad/vm/compiler/types.hpp>
#include <monad/vm/core/assert.h>
#include <monad/vm/core/cases.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <limits>
#include <utility>
#include <variant>
#include <vector>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::poly_typed;

using monad::vm::Cases;

namespace
{
    struct TypeError
    {
    };

    ContKind get_literal_cont(PolyTypedIR const &ir, uint256_t const &literal)
    {
        if (literal > uint256_t{std::numeric_limits<byte_offset>::max()}) {
            return cont_kind({}, 0);
        }
        byte_offset const off{literal[0]};
        auto jd = ir.jumpdests.find(off);
        if (jd == ir.jumpdests.end()) {
            return cont_kind({}, 0);
        }
        MONAD_VM_DEBUG_ASSERT(jd->second < ir.blocks.size());
        return ir.blocks[jd->second].kind;
    }

    Kind get_param_kind(Block const &block, size_t const param_id)
    {
        if (param_id >= block.kind->front.size()) {
            throw TypeError{};
        }
        return block.kind->front[param_id];
    }

    ContKind get_param_cont(Block const &block, size_t const param_id)
    {
        auto k = get_param_kind(block, param_id);
        if (std::holds_alternative<Cont>(*k)) {
            return std::get<Cont>(*k).cont;
        }
        if (std::holds_alternative<WordCont>(*k)) {
            return std::get<WordCont>(*k).cont;
        }
        throw TypeError{};
    }

    void check_dest(
        PolyTypedIR const &ir, Block const &block, Value const &dest,
        ContKind kind)
    {
        if (dest.is == ValueIs::LITERAL) {
            if (!can_specialize(get_literal_cont(ir, dest.literal), kind)) {
                throw TypeError{};
            }
        }
        else if (dest.is == ValueIs::PARAM_ID) {
            if (!weak_equal(get_param_cont(block, dest.param), kind)) {
                throw TypeError{};
            }
        }
        else {
            throw TypeError{};
        }
    }

    void check_output_value(
        PolyTypedIR const &ir, Block const &block, Value const &x, Kind k)
    {
        if (x.is == ValueIs::LITERAL) {
            std::visit(
                Cases{
                    [&](LiteralVar const &lv) {
                        if (!can_specialize(
                                get_literal_cont(ir, x.literal), lv.cont)) {
                            throw TypeError{};
                        }
                    },
                    [&](Cont const &c) {
                        if (!can_specialize(
                                get_literal_cont(ir, x.literal), c.cont)) {
                            throw TypeError{};
                        }
                    },
                    [&](WordCont const &wc) {
                        if (!can_specialize(
                                get_literal_cont(ir, x.literal), wc.cont)) {
                            throw TypeError{};
                        }
                    },
                    [&](Word const &) {
                        // nop
                    },
                    [&](auto const &) { throw TypeError{}; }},
                *k);
        }
        else if (x.is == ValueIs::PARAM_ID) {
            if (std::holds_alternative<Any>(*k)) {
                return;
            }
            auto p = get_param_kind(block, x.param);
            if (std::holds_alternative<WordCont>(*p) &&
                !std::holds_alternative<WordCont>(*k)) {
                if (std::holds_alternative<Word>(*k)) {
                    return;
                }
                if (!std::holds_alternative<Cont>(*k)) {
                    throw TypeError{};
                }
                if (!weak_equal(
                        std::get<WordCont>(*p).cont, std::get<Cont>(*k).cont)) {
                    throw TypeError{};
                }
            }
            else {
                if (!weak_equal(p, k)) {
                    throw TypeError{};
                }
            }
        }
        else {
            MONAD_VM_DEBUG_ASSERT(x.is == ValueIs::COMPUTED);
            if (!weak_equal(k, word)) {
                throw TypeError{};
            }
        }
    }

    void check_output_stack(
        Block const &block, size_t output_offset, ContKind out_kind,
        std::vector<Kind> const &output_stack)
    {
        MONAD_VM_DEBUG_ASSERT(block.output.size() >= output_offset);
        MONAD_VM_DEBUG_ASSERT(output_stack.size() >= block.output.size());
        size_t const min_size = std::min(
            output_stack.size() - output_offset, out_kind->front.size());
        for (size_t i = 0; i < min_size; ++i) {
            if (output_offset + i < block.output.size() &&
                block.output[output_offset + i].is == ValueIs::LITERAL) {
                if (!std::holds_alternative<Word>(
                        *output_stack[output_offset + i])) {
                    throw TypeError{};
                }
            }
            else {
                auto const &k1 = output_stack[output_offset + i];
                auto const &k2 = out_kind->front[i];
                if (std::holds_alternative<Any>(*k2)) {
                    continue;
                }
                if (std::holds_alternative<WordCont>(*k1)) {
                    if (std::holds_alternative<Cont>(*k2)) {
                        if (!weak_equal(
                                std::get<WordCont>(*k1).cont,
                                std::get<Cont>(*k2).cont)) {
                            throw TypeError{};
                        }
                    }
                    else if (!std::holds_alternative<Word>(*k2)) {
                        if (!weak_equal(k1, k2)) {
                            throw TypeError{};
                        }
                    }
                }
                else {
                    if (!weak_equal(k1, k2)) {
                        throw TypeError{};
                    }
                }
            }
        }
        if (output_stack.size() != out_kind->front.size() + output_offset) {
            if (!std::holds_alternative<ContWords>(out_kind->tail)) {
                throw TypeError{};
            }
            if (!std::holds_alternative<ContWords>(block.kind->tail)) {
                throw TypeError{};
            }
        }
        for (size_t i = min_size + output_offset; i < output_stack.size();
             ++i) {
            if (!weak_equal(output_stack[i], word)) {
                throw TypeError{};
            }
        }
        for (size_t i = min_size; i < out_kind->front.size(); ++i) {
            if (!weak_equal(out_kind->front[i], word)) {
                throw TypeError{};
            }
        }
    }

    void check_output(
        PolyTypedIR const &ir, Block const &block, size_t output_offset,
        ContKind out_kind, std::vector<Kind> const &output_stack)
    {
        check_output_stack(block, output_offset, out_kind, output_stack);
        MONAD_VM_DEBUG_ASSERT(block.output.size() >= output_offset);
        size_t const arg_count = block.output.size() - output_offset;
        std::vector<Kind> out_front = out_kind->front;
        if (out_front.size() < arg_count) {
            if (!std::holds_alternative<ContWords>(block.kind->tail)) {
                throw TypeError{};
            }
            do {
                out_front.push_back(word);
            }
            while (out_front.size() < arg_count);
        }

        for (size_t i = 0; i < arg_count; ++i) {
            check_output_value(
                ir, block, block.output[output_offset + i], out_front[i]);
        }

        size_t const n_left = out_front.size() - arg_count;
        if (block.kind->front.size() != n_left + block.min_params &&
            !std::holds_alternative<ContWords>(block.kind->tail)) {
            throw TypeError{};
        }
        std::vector<Kind> new_tail_front;
        for (size_t i = 0; i < n_left; ++i) {
            if (block.min_params + i < block.kind->front.size()) {
                new_tail_front.push_back(
                    block.kind->front[block.min_params + i]);
            }
            else {
                new_tail_front.push_back(word);
            }
        }
        std::vector<Kind> new_out_front;
        for (size_t i = arg_count; i < out_front.size(); ++i) {
            new_out_front.push_back(out_front[i]);
        }
        if (!weak_equal(
                cont_kind(std::move(new_tail_front), block.kind->tail),
                cont_kind(std::move(new_out_front), out_kind->tail))) {
            throw TypeError{};
        }
    }

    void check_block_not_word_typed(Block const &block)
    {
        if (std::holds_alternative<ContWords>(block.kind->tail)) {
            throw TypeError{};
        }
        std::visit(
            Cases{
                [](Jump const &t) {
                    if (std::holds_alternative<ContWords>(t.jump_kind->tail)) {
                        throw TypeError{};
                    }
                },
                [](JumpI const &t) {
                    if (std::holds_alternative<ContWords>(t.jump_kind->tail) ||
                        std::holds_alternative<ContWords>(
                            t.fallthrough_kind->tail)) {
                        throw TypeError{};
                    }
                },
                [](FallThrough const &t) {
                    if (std::holds_alternative<ContWords>(
                            t.fallthrough_kind->tail)) {
                        throw TypeError{};
                    }
                },
                [](auto const &) {
                    // nop
                }},
            block.terminator);
    }

    bool is_failed_block_kind(ContKind const &kind)
    {
        if (!kind->front.empty()) {
            return false;
        }
        return std::holds_alternative<ContWords>(kind->tail);
    }

    void check_block_has_failed_type(Block const &block)
    {
        if (!is_failed_block_kind(block.kind)) {
            throw TypeError{};
        }
        std::visit(
            Cases{
                [](Jump const &t) {
                    if (!is_failed_block_kind(t.jump_kind)) {
                        throw TypeError{};
                    }
                },
                [](JumpI const &t) {
                    if (!is_failed_block_kind(t.jump_kind) ||
                        !is_failed_block_kind(t.fallthrough_kind)) {
                        throw TypeError{};
                    }
                },
                [](FallThrough const &t) {
                    if (!is_failed_block_kind(t.fallthrough_kind)) {
                        throw TypeError{};
                    }
                },
                [](auto const &) { throw TypeError{}; }},
            block.terminator);
    }

    void check_instruction_pop(std::vector<Kind> &stack)
    {
        if (stack.empty()) {
            throw TypeError{};
        }
        stack.pop_back();
    }

    void check_instruction_swap(uint8_t ix, std::vector<Kind> &stack)
    {
        std::swap(stack[stack.size() - 1], stack[stack.size() - 1 - ix]);
    }

    void check_instruction_dup(uint8_t ix, std::vector<Kind> &stack)
    {
        stack.push_back(stack[stack.size() - ix]);
    }

    void
    check_instruction_default(Instruction const &ins, std::vector<Kind> &stack)
    {
        if (stack.size() < ins.stack_args()) {
            throw TypeError{};
        }
        std::vector<Kind> const front;
        for (size_t i = 0; i < ins.stack_args(); ++i) {
            if (!std::holds_alternative<Word>(*stack.back()) &&
                !std::holds_alternative<WordCont>(*stack.back())) {
                throw TypeError{};
            }
            stack.pop_back();
        }
        if (ins.increases_stack()) {
            stack.push_back(word);
        }
    }

    void check_instruction(Instruction const &ins, std::vector<Kind> &stack)
    {
        using enum OpCode;

        switch (ins.opcode()) {
        case Pop:
            return check_instruction_pop(stack);
        case Swap:
            return check_instruction_swap(ins.index(), stack);
        case Dup:
            return check_instruction_dup(ins.index(), stack);
        default:
            return check_instruction_default(ins, stack);
        }
    }

    std::vector<Kind> check_instructions(Block const &block)
    {
        std::vector<Kind> stack = block.kind->front;
        if (std::holds_alternative<ContWords>(block.kind->tail)) {
            while (stack.size() < block.min_params) {
                stack.push_back(word);
            }
        }
        std::reverse(stack.begin(), stack.end());
        for (auto const &ins : block.instrs) {
            check_instruction(ins, stack);
        }
        std::reverse(stack.begin(), stack.end());
        return stack;
    }

    void check_block_exact(PolyTypedIR const &ir, Block const &block)
    {
        std::vector<Kind> const output_stack = check_instructions(block);
        if (std::holds_alternative<Jump>(block.terminator)) {
            MONAD_VM_DEBUG_ASSERT(!block.output.empty());
            auto const &jump = std::get<Jump>(block.terminator);
            check_dest(ir, block, block.output[0], jump.jump_kind);
            check_output(ir, block, 1, jump.jump_kind, output_stack);
        }
        else if (std::holds_alternative<JumpI>(block.terminator)) {
            MONAD_VM_DEBUG_ASSERT(block.output.size() >= 2);
            auto const &jumpi = std::get<JumpI>(block.terminator);
            check_dest(ir, block, block.output[0], jumpi.jump_kind);
            check_output(ir, block, 2, jumpi.jump_kind, output_stack);
            if (!can_specialize(
                    ir.blocks[jumpi.fallthrough_dest].kind,
                    jumpi.fallthrough_kind)) {
                throw TypeError{};
            }
            check_output(ir, block, 2, jumpi.fallthrough_kind, output_stack);
        }
        else if (std::holds_alternative<FallThrough>(block.terminator)) {
            auto const &fall = std::get<FallThrough>(block.terminator);
            if (!can_specialize(
                    ir.blocks[fall.fallthrough_dest].kind,
                    fall.fallthrough_kind)) {
                throw TypeError{};
            }
            check_output(ir, block, 0, fall.fallthrough_kind, output_stack);
        }
        else {
            // It should not be possible to have Word.. tail with "exit"
            // terminator:
            check_block_not_word_typed(block);
        }
    }

    void check_block(PolyTypedIR const &ir, Block const &block)
    {
        try {
            check_block_exact(ir, block);
        }
        catch (TypeError const &) {
            check_block_has_failed_type(block);
        }
    }
}

namespace monad::vm::compiler::poly_typed
{
    PolyTypedIR::PolyTypedIR(local_stacks::LocalStacksIR const &&ir)
        : codesize{ir.codesize}
        , jumpdests{std::move(ir.jumpdests)}
        , blocks{infer_types(jumpdests, ir.blocks)}
    {
    }

    void PolyTypedIR::type_check_or_throw()
    {
        for (auto const &b : blocks) {
            check_block(*this, b);
        }
    }

    bool PolyTypedIR::type_check()
    {
        try {
            type_check_or_throw();
        }
        catch (TypeError const &) {
            return false;
        }
        return true;
    }
}

std::format_context::iterator std::formatter<PolyTypedIR>::format(
    PolyTypedIR const &ir, std::format_context &ctx) const
{
    for (auto const &b : ir.blocks) {
        std::format_to(ctx.out(), "0x{:x}:\n", b.offset);
        std::format_to(ctx.out(), "    {}\n", b.kind);
        if (ir.jumpdests.contains(b.offset)) {
            std::format_to(ctx.out(), "  JUMPDEST\n", b.offset);
        }
        for (auto const &ins : b.instrs) {
            std::format_to(ctx.out(), "  {}\n", ins);
        }
        std::format_to(ctx.out(), " =>");
        for (auto const &v : b.output) {
            std::format_to(ctx.out(), " {}", v);
        }
        std::format_to(ctx.out(), "\n");
        std::visit<void>(
            Cases{
                [&](JumpI const &t) {
                    std::format_to(ctx.out(), "  JUMPI\n");
                    std::format_to(ctx.out(), "  : {}\n", t.jump_kind);
                    std::format_to(ctx.out(), "  : {}\n", t.fallthrough_kind);
                },
                [&](Jump const &t) {
                    std::format_to(ctx.out(), "  JUMP\n");
                    std::format_to(ctx.out(), "  : {}\n", t.jump_kind);
                },
                [&](FallThrough const &t) {
                    std::format_to(ctx.out(), "  FALLTHROUGH\n");
                    std::format_to(ctx.out(), "  : {}\n", t.fallthrough_kind);
                },
                [&](Return const &) {
                    std::format_to(ctx.out(), "  RETURN\n");
                },
                [&](Revert const &) {
                    std::format_to(ctx.out(), "  REVERT\n");
                },
                [&](SelfDestruct const &) {
                    std::format_to(ctx.out(), "  SELFDESTRUCT\n");
                },
                [&](Stop const &) { std::format_to(ctx.out(), "  STOP\n"); },
                [&](InvalidInstruction const &) {
                    std::format_to(ctx.out(), "  INVALIDINSTRUCTION\n");
                },
            },
            b.terminator);
    }
    return ctx.out();
}
