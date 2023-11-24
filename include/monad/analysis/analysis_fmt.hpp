#pragma once

#include <monad/analysis/analysis.hpp>

#include <monad/core/basic_formatter.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/core/variant.hpp>

template <>
struct fmt::formatter<monad::analysis::Instruction>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::Instruction const &instruction,
        FormatContext &ctx) const
    {
        auto const *instruction_name =
            evmone::instr::traits[instruction.opcode].name;
        constexpr auto remove_leading_zeros = [](auto data) {
            if (data == monad::bytes32_t{}) {
                return fmt::format("0x00");
            }
            auto const hex_string = fmt::format("{}", data);
            std::string_view input{hex_string};
            size_t first_non_zero = 0;
            if (input.starts_with("0x")) {
                input.remove_prefix(2);
            }
            while (first_non_zero < input.size() &&
                   input[first_non_zero] == '0') {
                first_non_zero++;
            }
            auto const trimmed = input.substr(first_non_zero);
            return fmt::format("0x{}", trimmed);
        };
        return fmt::format_to(
            ctx.out(),
            "Instruction {{ 0x{:02x}, {}{} }}",
            instruction.offset,
            std::string{"OP_"} +
                (instruction_name != nullptr ? instruction_name : "null"),
            (instruction.opcode >= evmone::Opcode::OP_PUSH0 &&
             instruction.opcode <= evmone::Opcode::OP_PUSH32)
                ? fmt::format(
                      ", {}_bytes32", remove_leading_zeros(instruction.data))
                : "");
    }
};

template <>
struct fmt::formatter<monad::analysis::ControlFlow>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::ControlFlow const &control_flow,
        FormatContext &ctx) const
    {
        using monad::overloaded;
        using namespace monad::analysis;
        using Return = std::string;
        return fmt::format_to(
            ctx.out(),
            "ControlFlow {{ {} }}",
            std::visit(
                overloaded{
                    [](ResolvedControlFlow const &resolved) -> Return {
                        return std::visit(
                            overloaded{
                                [](Linear const &linear) -> Return {
                                    return fmt::format(
                                        "Linear {{ {} }}",
                                        linear.next_basic_block);
                                },
                                [](ResolvedStatic const &resolved_static)
                                    -> Return {
                                    return fmt::format(
                                        "ResolvedStatic {{ {} }}",
                                        resolved_static.target);
                                },
                                [](ResolvedDynamic const &resolved_dynamic)
                                    -> Return {
                                    return fmt::format(
                                        "ResolvedDynamic {{ {}, {} }}",
                                        resolved_dynamic.taken_target,
                                        resolved_dynamic.not_taken_target);
                                },
                                [](Halting const &) -> Return {
                                    return "Halting {}";
                                }},
                            resolved);
                    },
                    [](UnresolvedControlFlow const &unresolved) -> Return {
                        return std::visit(
                            overloaded{
                                [](UnresolvedDynamic const &unresolved_dynamic)
                                    -> Return {
                                    return fmt::format(
                                        "UnresolvedDynamic {{ {} }}",
                                        unresolved_dynamic.next_basic_block);
                                },
                                [](UnresolvedStatic const &) -> Return {
                                    return "UnresolvedStatic {}";
                                }},
                            unresolved);
                    }},
                control_flow));
    }
};

template <>
struct fmt::formatter<monad::analysis::BasicBlock>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::BasicBlock const &basic_block,
        FormatContext &ctx) const
    {
        return fmt::format_to(
            ctx.out(),
            "BasicBlock {{ {}, {}}}",
            basic_block.instructions,
            basic_block.control_flow);
    }
};

template <>
struct fmt::formatter<monad::analysis::Instructions>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::Instructions const &instructions,
        FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "Instructions {{");

        for (auto const &instruction : instructions) {
            fmt::format_to(ctx.out(), "{}, ", instruction);
        }

        if (!instructions.empty()) {
            fmt::format_to(ctx.out(), "\b\b");
        }

        return fmt::format_to(ctx.out(), " }}");
    }
};

template <>
struct fmt::formatter<monad::analysis::ControlFlowGraph>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::ControlFlowGraph const &graph,
        FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "ControlFlowGraph {{");

        for (auto const &[index, basic_block] : graph) {
            fmt::format_to(ctx.out(), "{{{}, {}}}, ", index, basic_block);
        }

        if (!graph.empty()) {
            fmt::format_to(ctx.out(), "\b\b");
        }

        return fmt::format_to(ctx.out(), " }}");
    }
};
