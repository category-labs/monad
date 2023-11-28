#pragma once

#include <monad/analysis/ssa.hpp>

#include <monad/core/basic_formatter.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/core/variant.hpp>

#include <evmone/instructions_traits.hpp>

template <>
struct fmt::formatter<monad::analysis::ConcreteValue>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::ConcreteValue const &concrete_value,
        FormatContext &ctx) const
    {
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
            "ConcreteValue {{ {}_bytes32 }}",
            remove_leading_zeros(concrete_value.value));
    }
};

template <>
struct fmt::formatter<monad::analysis::PlaceholderValue>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::PlaceholderValue const &placeholder_value,
        FormatContext &ctx) const
    {
        return fmt::format_to(
            ctx.out(),
            "PlaceholderValue {{ {} }}",
            placeholder_value.stack_offset);
    }
};

template <>
struct fmt::formatter<monad::analysis::Register> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::Register const &register_name,
        FormatContext &ctx) const
    {
        return fmt::format_to(
            ctx.out(), "Register {{ {} }}", register_name.register_name);
    }
};

template <>
struct fmt::formatter<monad::analysis::StackValue>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::StackValue const &stack_value,
        FormatContext &ctx) const
    {
        using monad::overloaded;
        using namespace monad::analysis;
        return fmt::format_to(
            ctx.out(),
            "StackValue {{ {} }}",
            std::visit(
                overloaded{
                    [](ConcreteValue const &concrete_value) {
                        return fmt::format("{}", concrete_value);
                    },
                    [](PlaceholderValue const &placeholder_value) {
                        return fmt::format("{}", placeholder_value);
                    },
                    [](Register const &register_name) {
                        return fmt::format("{}", register_name);
                    }},
                stack_value.value));
    }
};

template <>
struct fmt::formatter<monad::analysis::Arguments>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::Arguments const &arguments, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "Arguments {{");

        for (auto const &instruction : arguments) {
            fmt::format_to(ctx.out(), "{}, ", instruction);
        }

        if (!arguments.empty()) {
            fmt::format_to(ctx.out(), "\b\b");
        }

        return fmt::format_to(ctx.out(), " }}");
    }
};

template <>
struct fmt::formatter<monad::analysis::SSAInstruction>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::SSAInstruction const &instruction,
        FormatContext &ctx) const
    {
        auto const *instruction_name =
            evmone::instr::traits[instruction.opcode].name;
        return fmt::format_to(
            ctx.out(),
            "SSAInstruction {{ 0x{:02x}, {}, {}, {} }}",
            instruction.offset,
            std::string{"OP_"} +
                (instruction_name != nullptr ? instruction_name : "null"),
            instruction.arguments,
            instruction.return_value.has_value()
                ? fmt::format("{}", *instruction.return_value)
                : "std::nullopt");
    }
};

template <>
struct fmt::formatter<monad::analysis::SSAInstructions>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::SSAInstructions const &instructions,
        FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "SSAInstructions {{");

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
struct fmt::formatter<monad::analysis::SymbolicStack>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::SymbolicStack const &stack, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "SymbolicStack {{");

        for (auto const &stack_value : stack) {
            fmt::format_to(ctx.out(), "{}, ", stack_value);
        }

        if (!stack.empty()) {
            fmt::format_to(ctx.out(), "\b\b");
        }

        return fmt::format_to(ctx.out(), " }}");
    }
};

template <>
struct fmt::formatter<monad::analysis::SSABasicBlock>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::SSABasicBlock const &basic_block,
        FormatContext &ctx) const
    {
        return fmt::format_to(
            ctx.out(),
            "SSABasicBlock {{ {}, {}, {} }}",
            basic_block.instructions,
            basic_block.control_flow,
            basic_block.stack);
    }
};

template <>
struct fmt::formatter<monad::analysis::SSAControlFlowGraph>
    : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::SSAControlFlowGraph const &graph,
        FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "SSAControlFlowGraph {{");

        for (auto const &[index, basic_block] : graph) {
            fmt::format_to(ctx.out(), "{{{}, {}}}, ", index, basic_block);
        }

        if (!graph.empty()) {
            fmt::format_to(ctx.out(), "\b\b");
        }

        return fmt::format_to(ctx.out(), " }}");
    }
};
