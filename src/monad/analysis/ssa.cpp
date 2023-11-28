#include <monad/analysis/analysis.hpp>
#include <monad/analysis/analysis_fmt.hpp>
#include <monad/analysis/config.hpp>
#include <monad/analysis/ssa.hpp>
#include <monad/core/assert.h>

#include <optional>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <variant>

#include <evmone/instructions_opcodes.hpp>
#include <evmone/instructions_traits.hpp>

MONAD_ANALYSIS_NAMESPACE_BEGIN

StackValue::StackValue(StackValue::Variant value)
    : value{value}
{
}

SymbolicStack create_prefilled_stack()
{
    static constexpr auto NUMBER_OF_PREFILLED_STACK_ITEMS = 32;
    SymbolicStack stack;
    for (int i = NUMBER_OF_PREFILLED_STACK_ITEMS; i > 0; i--) {
        stack.emplace_back(PlaceholderValue{.stack_offset = -i});
    }
    return stack;
}

[[nodiscard]] bool resolve_phis(SSAControlFlowGraph &control_flow_graph)
{
    bool dirty = false;

    for (auto const &[block_index, basic_block] : control_flow_graph) {
        for (auto const &instruction : basic_block.instructions) {
            instruction.resolve_arguments();
        }
    }
    return false;
}

[[nodiscard]] bool handle_writers(SSAInstruction const *writer, int depth)
{
    if (depth == 0) {
        return false;
    }
    bool dirty = false;

    if (is_push(writer->opcode)) {
        MONAD_DEBUG_ASSERT(!writer->arguments.empty());
        [[maybe_unused]] auto const value = writer->arguments[0];
        // dirty |= block.add_jump_target(value)
    }
}

[[nodiscard]] bool
resolve_cross_references(SSAControlFlowGraph &control_flow_graph)
{
    using enum evmone::Opcode;
    bool dirty = false;

    for (auto const &[block_index, basic_block] : control_flow_graph) {
        if (basic_block.instructions.empty()) {
            continue;
        }

        auto const &last_instruction = basic_block.instructions.back();

        if (last_instruction.opcode == OP_JUMP ||
            last_instruction.opcode == OP_JUMPI) {
            MONAD_DEBUG_ASSERT(!last_instruction.arguments.empty());
            auto const target = last_instruction.arguments[0];

            if (!std::holds_alternative<PlaceholderValue>(target.value) &&
                target.writer != nullptr) {
                dirty |= handle_writers(target.writer, 5);
            }
        }
    }

    return dirty;
}

[[nodiscard]] SSAControlFlowGraph
lift_cfg_to_ssa(ControlFlowGraph const &control_flow_graph)
{
    using enum evmone::Opcode;
    SSAControlFlowGraph result;
    size_t global_value_name = 0;
    for (auto const &[block_index, basic_block] : control_flow_graph) {
        auto stack = create_prefilled_stack();
        SSAInstructions ssa_instructions{};
        ssa_instructions.reserve(basic_block.instructions.size());
        for (auto const &instruction : basic_block.instructions) {
            auto const opcode = instruction.opcode;
            auto const stack_reach =
                evmone::instr::traits[opcode].stack_height_required;
            if (is_push(opcode)) {
                ssa_instructions.emplace_back(SSAInstruction{
                    .offset = instruction.offset,
                    .opcode = instruction.opcode,
                    .arguments = {StackValue{
                        ConcreteValue{.value = instruction.data}}},
                    .return_value = global_value_name});
                stack.emplace_back(
                    Register{.register_name = global_value_name});
                global_value_name++;
                continue;
            }
            if (is_dup(opcode)) {
                if (std::cmp_less(stack.size(), stack_reach - 1)) {
                    throw std::runtime_error(fmt::format(
                        "tried to reach into {} of a stack height {} while "
                        "processing instruction {}",
                        stack_reach - 1,
                        stack.size(),
                        instruction));
                }

                MONAD_ASSERT(stack_reach > 0);
                auto const signed_dup_offset = static_cast<size_t>(stack_reach);
                stack.push_back(stack.at(stack.size() - signed_dup_offset));
                continue;
            }
            if (is_swap(opcode)) {
                MONAD_ASSERT(stack_reach > 0);
                auto const signed_swap_offset =
                    static_cast<size_t>(stack_reach);
                std::swap(
                    stack.at(stack.size() - 1),
                    stack.at(stack.size() - signed_swap_offset - 1));
                continue;
            }
            if (opcode == OP_POP) {
                MONAD_ASSERT(!stack.empty());
                stack.pop_back();
                continue;
            }
            if (opcode == OP_JUMPDEST) {
                continue;
            }

            auto const stack_height_change =
                evmone::instr::traits[opcode].stack_height_change;
            Arguments arguments;
            for (int i = 0; i < stack_reach; i++) {
                MONAD_ASSERT(!stack.empty());
                arguments.emplace_back(stack.back().value);
                stack.pop_back();
            }
            std::optional<size_t> return_value;
            if (stack_height_change > 0) {
                return_value = global_value_name;
                stack.emplace_back(
                    Register{.register_name = global_value_name});
                global_value_name++;
            }

            ssa_instructions.emplace_back(SSAInstruction{
                .offset = instruction.offset,
                .opcode = instruction.opcode,
                .arguments = std::move(arguments),
                .return_value = return_value});
        }

        result.emplace(
            std::piecewise_construct,
            std::forward_as_tuple(block_index),
            std::forward_as_tuple(
                std::move(ssa_instructions),
                basic_block.control_flow,
                std::move(stack)));
    }
    return result;
}

UseDefGraph construct_use_def_graph(SSAControlFlowGraph const &)
{
    return {};
}

MONAD_ANALYSIS_NAMESPACE_END
