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
#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/compiler/ir/local_stacks.hpp>
#include <category/vm/compiler/ir/poly_typed/block.hpp>
#include <category/vm/compiler/ir/poly_typed/exceptions.hpp>
#include <category/vm/compiler/ir/poly_typed/infer.hpp>
#include <category/vm/compiler/ir/poly_typed/infer_state.hpp>
#include <category/vm/compiler/ir/poly_typed/kind.hpp>
#include <category/vm/compiler/ir/poly_typed/strongly_connected_components.hpp>
#include <category/vm/compiler/ir/poly_typed/unify.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>

#include <algorithm>
#include <cstddef>
#include <exception>
#include <limits>
#include <list>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

namespace
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::compiler::poly_typed;

    void subst_terminator(InferState &state, block_id bid)
    {
        using monad::vm::Cases;

        auto new_term = std::visit(
            Cases{
                [&state](FallThrough const &t) -> Terminator {
                    return FallThrough{
                        .fallthrough_kind =
                            state.subst_map.subst_or_throw(t.fallthrough_kind),
                        .fallthrough_dest = t.fallthrough_dest};
                },
                [&state](JumpI const &t) -> Terminator {
                    return JumpI{
                        .fallthrough_kind =
                            state.subst_map.subst_or_throw(t.fallthrough_kind),
                        .jump_kind =
                            state.subst_map.subst_or_throw(t.jump_kind),
                        .fallthrough_dest = t.fallthrough_dest};
                },
                [&state](Jump const &t) -> Terminator {
                    return Jump{state.subst_map.subst_or_throw(t.jump_kind)};
                },
                [](auto const &t) -> Terminator { return t; },
            },
            state.block_terminators.at(bid));

        state.block_terminators.insert_or_assign(bid, new_term);
    }

    ContKind initial_block_kind(
        InferState &state, block_id bid,
        std::unordered_map<block_id, std::vector<VarName>> &front_vars_map)
    {
        std::vector<Kind> front;
        size_t const n = state.pre_blocks[bid].min_params;
        auto &front_vars = front_vars_map[bid];
        for (size_t i = 0; i < n; ++i) {
            VarName const v = state.fresh_kind_var();
            front_vars.push_back(v);
            front.push_back(kind_var(v));
        }
        return cont_kind(std::move(front), state.fresh_cont_var());
    }

    void infer_instruction_pop(std::vector<Kind> &stack)
    {
        MONAD_VM_DEBUG_ASSERT(!stack.empty());
        stack.pop_back();
    }

    void
    infer_instruction_swap(Instruction const &ins, std::vector<Kind> &stack)
    {
        size_t const ix = ins.index();
        MONAD_VM_DEBUG_ASSERT(stack.size() > ix);
        std::swap(stack[stack.size() - 1], stack[stack.size() - 1 - ix]);
    }

    void infer_instruction_dup(Instruction const &ins, std::vector<Kind> &stack)
    {
        size_t const ix = ins.index();
        MONAD_VM_DEBUG_ASSERT(stack.size() >= ix);
        stack.push_back(stack[stack.size() - ix]);
    }

    void infer_instruction_default(
        InferState &state, Instruction const &ins, std::vector<Kind> &stack)
    {
        MONAD_VM_DEBUG_ASSERT(stack.size() >= ins.stack_args());
        std::vector<Kind> const front;
        for (size_t i = 0; i < ins.stack_args(); ++i) {
            unify(state.subst_map, stack.back(), word);
            stack.pop_back();
        }
        if (ins.increases_stack()) {
            stack.push_back(word);
        }
    }

    void infer_instruction(
        InferState &state, Instruction const &ins, std::vector<Kind> &stack)
    {
        using enum OpCode;

        switch (ins.opcode()) {
        case Pop:
            return infer_instruction_pop(stack);
        case Swap:
            return infer_instruction_swap(ins, stack);
        case Dup:
            return infer_instruction_dup(ins, stack);
        default:
            return infer_instruction_default(state, ins, stack);
        }
    }

    void push_literal_output(
        InferState &state, Component const &component, std::vector<Kind> &front,
        Kind &&k, Value const &value, size_t jumpix)
    {
        MONAD_VM_DEBUG_ASSERT(alpha_equal(k, word));
        auto b = state.get_jumpdest(value);
        if (!b.has_value()) {
            // Invalid jump
            front.push_back(literal_var(
                state.fresh_literal_var(),
                cont_kind({}, state.fresh_cont_var())));
            return;
        }
        if (jumpix != std::numeric_limits<size_t>::max() &&
            component.contains(*b)) {
            // Recursive is assumed to be word if it appears as argument to a
            // continuation (parameter).
            front.push_back(std::move(k));
            return;
        }
        front.push_back(
            literal_var(state.fresh_literal_var(), state.get_type(*b)));
    }

    void push_param_output(
        InferState &state, ParamVarNameMap &param_map, std::vector<Kind> &front,
        Kind &&k, size_t const &param, size_t jumpix)
    {
        if (param == jumpix) {
            front.push_back(std::move(k));
        }
        else {
            VarName const v = state.fresh_kind_var();
            param_map[param].push_back(v);
            front.push_back(kind_var(v));
        }
    }

    ContKind block_output_kind(
        InferState &state, ParamVarNameMap &param_map,
        Component const &component, size_t offset,
        local_stacks::Block const &block, std::vector<Kind> &&stack,
        ContTailKind tail, size_t jumpix)
    {
        MONAD_VM_DEBUG_ASSERT(stack.size() == block.output.size());
        MONAD_VM_DEBUG_ASSERT(stack.size() >= offset);
        std::vector<Kind> front;
        for (size_t oix = offset, six = stack.size() - offset; six > 0; ++oix) {
            --six;
            switch (block.output[oix].is) {
            case ValueIs::LITERAL:
                push_literal_output(
                    state,
                    component,
                    front,
                    std::move(stack[six]),
                    block.output[oix],
                    jumpix);
                break;
            case ValueIs::PARAM_ID:
                push_param_output(
                    state,
                    param_map,
                    front,
                    std::move(stack[six]),
                    block.output[oix].param,
                    jumpix);
                break;
            case ValueIs::COMPUTED:
                front.push_back(std::move(stack[six]));
                break;
            }
        }
        return cont_kind(std::move(front), tail);
    }

    Kind infer_terminator_jumpi(
        InferState &state, ParamVarNameMap &param_map,
        Component const &component, block_id bid, std::vector<Kind> &&stack,
        ContTailKind tail)
    {
        MONAD_VM_DEBUG_ASSERT(stack.size() >= 2);
        unify(state.subst_map, stack[stack.size() - 2], word);
        Kind jumpdest = stack.back();
        auto jump_stack = stack;
        auto const jump_tail = tail;
        auto const &block = state.pre_blocks[bid];
        MONAD_VM_DEBUG_ASSERT(block.output.size() >= 2);
        size_t jumpix = std::numeric_limits<size_t>::max();
        if (block.output[0].is == local_stacks::ValueIs::PARAM_ID) {
            jumpix = block.output[0].param;
        }
        state.block_terminators.insert_or_assign(
            bid,
            JumpI{
                .fallthrough_kind = block_output_kind(
                    state,
                    param_map,
                    component,
                    2,
                    block,
                    std::move(stack),
                    tail,
                    jumpix),
                .jump_kind = block_output_kind(
                    state,
                    param_map,
                    component,
                    2,
                    block,
                    std::move(jump_stack),
                    jump_tail,
                    jumpix),
                .fallthrough_dest = block.fallthrough_dest,
            });
        return jumpdest;
    }

    Kind infer_terminator_jump(
        InferState &state, ParamVarNameMap &param_map,
        Component const &component, block_id bid, std::vector<Kind> &&stack,
        ContTailKind tail)
    {
        MONAD_VM_DEBUG_ASSERT(stack.size() >= 1);
        Kind jumpdest = stack.back();
        auto const &block = state.pre_blocks[bid];
        MONAD_VM_DEBUG_ASSERT(block.output.size() >= 1);
        size_t jumpix = std::numeric_limits<size_t>::max();
        if (block.output[0].is == local_stacks::ValueIs::PARAM_ID) {
            jumpix = block.output[0].param;
        }
        state.block_terminators.insert_or_assign(
            bid,
            Jump{
                .jump_kind = block_output_kind(
                    state,
                    param_map,
                    component,
                    1,
                    block,
                    std::move(stack),
                    tail,
                    jumpix),
            });
        return jumpdest;
    }

    Kind infer_terminator_fallthrough(
        InferState &state, ParamVarNameMap &param_map,
        Component const &component, block_id bid, std::vector<Kind> &&stack,
        ContTailKind tail)
    {
        auto const &block = state.pre_blocks[bid];
        size_t const jumpix = std::numeric_limits<size_t>::max();
        state.block_terminators.insert_or_assign(
            bid,
            FallThrough{
                block_output_kind(
                    state,
                    param_map,
                    component,
                    0,
                    block,
                    std::move(stack),
                    tail,
                    jumpix),
                block.fallthrough_dest});
        return any; // should never be used
    }

    Kind infer_terminator_return(
        InferState &state, block_id bid, std::vector<Kind> &&stack)
    {
        MONAD_VM_DEBUG_ASSERT(stack.size() >= 2);
        unify(state.subst_map, stack[stack.size() - 1], word);
        unify(state.subst_map, stack[stack.size() - 2], word);
        state.block_terminators.insert_or_assign(bid, Return{});
        return any; // should never be used
    }

    Kind infer_terminator_revert(
        InferState &state, block_id bid, std::vector<Kind> &&stack)
    {
        MONAD_VM_DEBUG_ASSERT(stack.size() >= 2);
        unify(state.subst_map, stack[stack.size() - 1], word);
        unify(state.subst_map, stack[stack.size() - 2], word);
        state.block_terminators.insert_or_assign(bid, Revert{});
        return any; // should never be used
    }

    Kind infer_terminator_stop(InferState &state, block_id bid)
    {
        state.block_terminators.insert_or_assign(bid, Stop{});
        return any; // should never be used
    }

    Kind infer_terminator_self_destruct(
        InferState &state, block_id bid, std::vector<Kind> &&stack)
    {
        MONAD_VM_DEBUG_ASSERT(stack.size() >= 1);
        unify(state.subst_map, stack.back(), word);
        state.block_terminators.insert_or_assign(bid, SelfDestruct{});
        return any; // should never be used
    }

    Kind infer_terminator_invalid_instruction(InferState &state, block_id bid)
    {
        state.block_terminators.insert_or_assign(bid, InvalidInstruction{});
        return any; // should never be used
    }

    Kind infer_terminator(
        InferState &state, ParamVarNameMap &param_map,
        Component const &component, block_id bid, basic_blocks::Terminator term,
        std::vector<Kind> &&stack, ContTailKind tail)
    {
        switch (term) {
        case basic_blocks::Terminator::FallThrough:
            return infer_terminator_fallthrough(
                state, param_map, component, bid, std::move(stack), tail);
        case basic_blocks::Terminator::JumpI:
            return infer_terminator_jumpi(
                state, param_map, component, bid, std::move(stack), tail);
        case basic_blocks::Terminator::Jump:
            return infer_terminator_jump(
                state, param_map, component, bid, std::move(stack), tail);
        case basic_blocks::Terminator::Return:
            return infer_terminator_return(state, bid, std::move(stack));
        case basic_blocks::Terminator::Stop:
            return infer_terminator_stop(state, bid);
        case basic_blocks::Terminator::Revert:
            return infer_terminator_revert(state, bid, std::move(stack));
        case basic_blocks::Terminator::SelfDestruct:
            return infer_terminator_self_destruct(state, bid, std::move(stack));
        case basic_blocks::Terminator::InvalidInstruction:
            return infer_terminator_invalid_instruction(state, bid);
        }
        std::terminate();
    }

    Kind infer_block_start(
        InferState &state, Component const &component,
        ParamVarNameMap &param_map, block_id bid)
    {
        ContKind const cont = state.block_types.at(bid);
        std::vector<Kind> stack = cont->front;
        std::reverse(stack.begin(), stack.end());
        auto const &block = state.pre_blocks[bid];
        for (auto const &ins : block.instrs) {
            infer_instruction(state, ins, stack);
        }
        return infer_terminator(
            state,
            param_map,
            component,
            bid,
            block.terminator,
            std::move(stack),
            cont->tail);
    }

    struct BlockTypeSpec
    {
        block_id bid;
        Kind jumpdest;
        ParamVarNameMap param_map;
        std::vector<VarName> front_vars;
    };

    using ComponentTypeSpec = std::vector<BlockTypeSpec>;

    void infer_block_jump_literal(
        InferState &state, Value const &dest, ContKind out_kind)
    {
        std::optional<block_id> did = state.get_jumpdest(dest);
        if (!did.has_value()) {
            // Invalid jump destination. Unify will always succeed.
            return;
        }
        unify(state.subst_map, state.get_type(*did), std::move(out_kind));
    }

    void infer_block_jump_param(
        InferState &state, BlockTypeSpec const &bts, ContKind *out_kind)
    {
        MONAD_VM_DEBUG_ASSERT(std::holds_alternative<KindVar>(*bts.jumpdest));
        Kind dest_kind = state.subst_map.subst_or_throw(bts.jumpdest);
        if (std::holds_alternative<KindVar>(*dest_kind)) {
            state.subst_map.transaction();
            try {
                unify(state.subst_map, dest_kind, cont(*out_kind));
                state.subst_map.commit();
            }
            catch (UnificationException const &) {
                state.subst_map.revert();
                VarName const v = std::get<KindVar>(*dest_kind).var;
                state.subst_map.insert_kind(v, any);
                *out_kind = state.subst_map.subst_or_throw(*out_kind);
                state.subst_map.insert_kind(v, cont(*out_kind));
            }
        }
        else if (std::holds_alternative<Word>(*dest_kind)) {
            VarName const v = state.subst_map.subst_to_var(bts.jumpdest);
            *out_kind = state.subst_map.subst_or_throw(*out_kind);
            state.subst_map.insert_kind(v, word_cont(*out_kind));
        }
        else if (std::holds_alternative<WordCont>(*dest_kind)) {
            unify(
                state.subst_map,
                std::get<WordCont>(*dest_kind).cont,
                *out_kind);
        }
        else {
            unify(state.subst_map, std::move(dest_kind), cont(*out_kind));
        }
    }

    void infer_block_jump(
        InferState &state, BlockTypeSpec const &bts, ContKind *out_kind)
    {
        auto const &block = state.pre_blocks[bts.bid];
        MONAD_VM_DEBUG_ASSERT(!block.output.empty());
        Value const &dest = block.output[0];
        switch (dest.is) {
        case ValueIs::LITERAL:
            return infer_block_jump_literal(state, dest, *out_kind);
        case ValueIs::PARAM_ID:
            return infer_block_jump_param(state, bts, out_kind);
        case ValueIs::COMPUTED:
            throw UnificationException{};
        }
        std::terminate();
    }

    void
    infer_block_fallthrough(InferState &state, block_id dest, ContKind out_kind)
    {
        unify(state.subst_map, state.get_type(dest), std::move(out_kind));
    }

    void unify_out_kind_literal_vars(
        InferState &state, Component const &component, BlockTypeSpec const &bts,
        size_t offset, ContKind out_kind)
    {
        auto const &block = state.pre_blocks[bts.bid];
        for (size_t oix = offset; oix < block.output.size(); ++oix) {
            auto b = state.get_jumpdest(block.output[oix]);
            if (!b.has_value() || !component.contains(*b)) {
                continue;
            }
            size_t const fix = oix - offset;
            Kind const &k = out_kind->front[fix];
            if (!std::holds_alternative<LiteralVar>(*k)) {
                continue;
            }
            unify(
                state.subst_map,
                state.get_type(*b),
                std::get<LiteralVar>(*k).cont);
        }
    }

    void infer_block_end(
        InferState &state, Component const &component, BlockTypeSpec const &bts)
    {
        Terminator &term = state.block_terminators.at(bts.bid);
        if (std::holds_alternative<Jump>(term)) {
            Jump &jump = std::get<Jump>(term);
            unify_out_kind_literal_vars(
                state, component, bts, 1, jump.jump_kind);
            infer_block_jump(state, bts, &jump.jump_kind);
        }
        else if (std::holds_alternative<JumpI>(term)) {
            JumpI &jumpi = std::get<JumpI>(term);
            unify_out_kind_literal_vars(
                state, component, bts, 2, jumpi.jump_kind);
            infer_block_jump(state, bts, &jumpi.jump_kind);
            unify_out_kind_literal_vars(
                state, component, bts, 2, jumpi.fallthrough_kind);
            infer_block_fallthrough(
                state, jumpi.fallthrough_dest, jumpi.fallthrough_kind);
        }
        else if (std::holds_alternative<FallThrough>(term)) {
            auto const &fall = std::get<FallThrough>(term);
            unify_out_kind_literal_vars(
                state, component, bts, 0, fall.fallthrough_kind);
            infer_block_fallthrough(
                state, fall.fallthrough_dest, fall.fallthrough_kind);
        }
        else {
            // Exit terminator unification will always succeed.
            state.block_types.insert_or_assign(
                bts.bid,
                state.subst_map.subst_or_throw(state.block_types.at(bts.bid)));
            return;
        }

        unify_param_var_name_map(
            state.subst_map, bts.front_vars, bts.param_map);

        state.block_types.insert_or_assign(
            bts.bid,
            state.subst_map.subst_or_throw(state.block_types.at(bts.bid)));
    }

    void sort_component_type_spec(
        InferState const &state, Component const &component,
        ComponentTypeSpec &cts)
    {
        MONAD_VM_DEBUG_ASSERT(cts.size() == component.size());
        MONAD_VM_DEBUG_ASSERT(!cts.empty());

        auto const &bts = cts[0];
        MONAD_VM_DEBUG_ASSERT(component.contains(bts.bid));

        std::list<block_id> order;

        std::vector<std::pair<block_id, std::list<block_id>::iterator>>
            work_stack;
        std::unordered_set<block_id> visited_set;
        work_stack.emplace_back(bts.bid, order.end());

        do {
            auto [b, it] = work_stack.back();
            work_stack.pop_back();
            if (!visited_set.contains(b)) {
                it = order.insert(it, b);
                visited_set.insert(b);
                for (block_id const s : state.static_successors(b)) {
                    if (component.contains(s)) {
                        work_stack.emplace_back(s, it);
                    }
                }
            }
        }
        while (!work_stack.empty());

        MONAD_VM_DEBUG_ASSERT(order.size() == cts.size());

        std::unordered_map<block_id, size_t> ordinals;
        auto order_it = order.begin();
        for (size_t i = 0; order_it != order.end(); ++i, ++order_it) {
            ordinals.insert_or_assign(*order_it, i);
        }

        std::sort(
            cts.begin(), cts.end(), [&ordinals](auto const &x, auto const &y) {
                return ordinals.at(x.bid) < ordinals.at(y.bid);
            });
    }

    void infer_recursive_component(
        InferState &state, Component const &component,
        ComponentTypeSpec const &cts)
    {
        // Given a recursive strongly connected component, the algorithm is to
        // repeat inference until we reach a fixed point. The intuition is that
        // for each inference iteration we have new type information, which the
        // inference iteration propagates through the basic blocks. If we cannot
        // reach a fixed point within a reasonable number of iterations, we give
        // up and throw `UnificationException`.

        MONAD_VM_DEBUG_ASSERT(!cts.empty());

        // We must infer types at least twice:
        for (size_t i = 0; i < 2; ++i) {
            for (auto const &bts : cts) {
                infer_block_end(state, component, bts);
            }
        }

        // Attempt to infer types until we reach a fixed point. It is common
        // that we have already reached a fixed point with the previous two
        // iterations.
        for (size_t i = 0; i < 5; ++i) {
            bool fixpoint_found = true;
            for (auto const &bts : cts) {
                auto orig_type = state.block_types.at(bts.bid);
                infer_block_end(state, component, bts);
                auto new_type = state.block_types.at(bts.bid);
                fixpoint_found &=
                    alpha_equal(std::move(orig_type), std::move(new_type));
            }
            if (fixpoint_found) {
                for (auto const &bts : cts) {
                    subst_terminator(state, bts.bid);
                }
                return;
            }
        }

        // We did not find a fixed point.
        throw UnificationException{};
    }

    void infer_non_recursive_component(
        InferState &state, Component const &component,
        ComponentTypeSpec const &cts)
    {
        MONAD_VM_DEBUG_ASSERT(cts.size() == 1);
        infer_block_end(state, component, cts[0]);
        block_id const bid = cts[0].bid;
        subst_terminator(state, bid);
    }

    void set_word_typed_component(InferState &state, Component const &component)
    {
        for (auto const bid : component) {
            state.block_types.insert_or_assign(bid, cont_words);
            auto const &block = state.pre_blocks[bid];
            switch (block.terminator) {
            case basic_blocks::Terminator::FallThrough:
                state.block_terminators.insert_or_assign(
                    bid, FallThrough{cont_words, block.fallthrough_dest});
                break;
            case basic_blocks::Terminator::JumpI:
                state.block_terminators.insert_or_assign(
                    bid, JumpI{cont_words, cont_words, block.fallthrough_dest});
                break;
            case basic_blocks::Terminator::Jump:
                state.block_terminators.insert_or_assign(bid, Jump{cont_words});
                break;
            default:
                break;
            }
        }
    }

    bool is_recursive_component(InferState &state, Component const &component)
    {
        if (component.size() > 1) {
            return true;
        }
        for (block_id const suc : state.static_successors(*component.begin())) {
            if (component.contains(suc)) {
                return true;
            }
        }
        return false;
    }

    void infer_component(InferState &state, Component const &component)
    {
        MONAD_VM_DEBUG_ASSERT(!component.empty());
        std::unordered_map<block_id, std::vector<VarName>> front_vars_map;
        state.reset();
        for (auto const bid : component) {
            __attribute__((unused)) bool const ins =
                state.block_types
                    .insert_or_assign(
                        bid, initial_block_kind(state, bid, front_vars_map))
                    .second;
            MONAD_VM_DEBUG_ASSERT(ins);
        }
        try {
            ComponentTypeSpec component_type_spec;
            for (auto const bid : component) {
                ParamVarNameMap param_map;
                Kind jumpdest =
                    infer_block_start(state, component, param_map, bid);
                component_type_spec.emplace_back(
                    bid,
                    std::move(jumpdest),
                    std::move(param_map),
                    std::move(front_vars_map.at(bid)));
            }
            if (is_recursive_component(state, component)) {
                sort_component_type_spec(state, component, component_type_spec);
                infer_recursive_component(
                    state, component, component_type_spec);
            }
            else {
                infer_non_recursive_component(
                    state, component, component_type_spec);
            }
        }
        catch (InferException const &) {
            set_word_typed_component(state, component);
        }
    }

    std::vector<Block> infer_components(
        InferState &state, std::vector<Component> const &components)
    {
        for (auto const &c : components) {
            infer_component(state, c);
        }
        std::vector<Block> blocks;
        blocks.reserve(state.pre_blocks.size());
        for (block_id i = 0; i < state.pre_blocks.size(); ++i) {
            auto &pre_block = state.pre_blocks[i];
            blocks.push_back(Block{
                .offset = pre_block.offset,
                .min_params = pre_block.min_params,
                .output = std::move(pre_block.output),
                .instrs = std::move(pre_block.instrs),
                .kind = std::move(state.block_types.at(i)),
                .terminator = std::move(state.block_terminators.at(i))});
        }
        return blocks;
    }

    void subst_block(SubstMap &su, Block &block)
    {
        // Since `su.subst_or_throw` has already been called in both
        // `infer_block_end` and `subst_terminator`, it is an invariant that
        // `su.subst_or_throw` will not throw in `subst_block`. Some
        // `LiteralVar`s may get substituted here, but this does not increase
        // substitution ticks or depth.
        block.kind = su.subst_or_throw(block.kind);
        if (std::holds_alternative<JumpI>(block.terminator)) {
            JumpI &jumpi = std::get<JumpI>(block.terminator);
            jumpi.jump_kind = su.subst_or_throw(jumpi.jump_kind);
            jumpi.fallthrough_kind = su.subst_or_throw(jumpi.fallthrough_kind);
        }
        else if (std::holds_alternative<Jump>(block.terminator)) {
            Jump &jump = std::get<Jump>(block.terminator);
            jump.jump_kind = su.subst_or_throw(jump.jump_kind);
        }
        else if (std::holds_alternative<FallThrough>(block.terminator)) {
            FallThrough &fall = std::get<FallThrough>(block.terminator);
            fall.fallthrough_kind = su.subst_or_throw(fall.fallthrough_kind);
        }
    }
}

namespace monad::vm::compiler::poly_typed
{
    std::vector<Block> infer_types(
        std::unordered_map<byte_offset, block_id> const &jumpdests,
        std::vector<local_stacks::Block> &&pre_blocks)
    {
        InferState state{jumpdests, std::move(pre_blocks)};
        auto const components = strongly_connected_components(state);
        std::vector<Block> blocks = infer_components(state, components);
        state.reset();
        for (auto &b : blocks) {
            // Substitute one last time to eliminate all the literal vars that
            // are assigned a literal type.
            subst_block(state.subst_map, b);
        }
        return blocks;
    }
}
