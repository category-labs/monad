#pragma once

#include <monad/analysis/config.hpp>

#include <monad/core/basic_formatter.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/likely.h>

#include <evmone/baseline.hpp>
#include <evmone/instructions.hpp>
#include <evmone/instructions_opcodes.hpp>
#include <evmone/instructions_traits.hpp>

#include <boost/graph/adjacency_list.hpp>

#include <format>
#include <map>
#include <optional>
#include <span>
#include <variant>
#include <vector>

MONAD_ANALYSIS_NAMESPACE_BEGIN

constexpr bool is_push(evmone::Opcode const opcode)
{
    return opcode >= evmone::Opcode::OP_PUSH0 &&
           opcode <= evmone::Opcode::OP_PUSH32;
}

constexpr bool is_dup(evmone::Opcode const opcode)
{
    return opcode >= evmone::Opcode::OP_DUP1 &&
           opcode <= evmone::Opcode::OP_DUP16;
}

constexpr bool is_swap(evmone::Opcode const opcode)
{
    return opcode >= evmone::Opcode::OP_SWAP1 &&
           opcode <= evmone::Opcode::OP_SWAP16;
}

struct Instruction
{
    Instruction(evmone::Opcode opcode);
    Instruction(evmone::Opcode opcode, bytes32_t data);
    Instruction(size_t offset, evmone::Opcode opcode, bytes32_t data);
    Instruction(size_t offset, evmone::Opcode opcode);

    bool operator==(Instruction const &rhs) const;
    bool operator!=(Instruction const &rhs) const;

    size_t const offset;

    evmone::Opcode const opcode;
    // TODO: for better performance, we can store immediate opcode data
    // separately since only push opcodes use it
    bytes32_t const data;
};

using Instructions = std::vector<Instruction>;
using InstructionsView = std::span<Instruction const>;

struct UnresolvedStatic
{
    friend bool
    operator==(UnresolvedStatic const &, UnresolvedStatic const &) = default;
};

struct ResolvedStatic
{
    size_t target;

    friend bool
    operator==(ResolvedStatic const &, ResolvedStatic const &) = default;
};

struct UnresolvedDynamic
{
    size_t next_basic_block;

    friend bool
    operator==(UnresolvedDynamic const &, UnresolvedDynamic const &) = default;
};

struct ResolvedDynamic
{
    size_t taken_target;
    size_t not_taken_target;

    friend bool
    operator==(ResolvedDynamic const &, ResolvedDynamic const &) = default;
};

struct Halting
{
    friend bool operator==(Halting const &, Halting const &) = default;
};

struct Linear
{
    size_t next_basic_block;

    friend bool operator==(Linear const &, Linear const &) = default;
};

using ResolvedControlFlow =
    std::variant<Linear, ResolvedStatic, ResolvedDynamic, Halting>;
using UnresolvedControlFlow = std::variant<UnresolvedDynamic, UnresolvedStatic>;

using ControlFlow = std::variant<ResolvedControlFlow, UnresolvedControlFlow>;

struct BasicBlock
{
    BasicBlock(InstructionsView instructions_view, ControlFlow control_flow);

    [[nodiscard]] std::optional<size_t> get_indirect_branch() const;
    [[nodiscard]] std::optional<size_t> get_next_basic_block() const;
    [[nodiscard]] bool is_control_flow_resolved() const;

    Instructions instructions;
    ControlFlow control_flow;
};

using JumpDestinations = std::map<bytes32_t, size_t>;
using ControlFlowGraph = std::map<size_t, BasicBlock>;

/**
 * Pad code to protect against a PUSH at the end of an instruction stream that
 * would result in reading out of bounds.
 * For example: PUSH32 0xdeadbeef at the end of an instruction stream.
 * @param code
 * @return
 */
auto pad_code(byte_string code) -> byte_string;

/**
 * @param code
 * @return a pair
 * - tokenized list of opcodes.
 * - a map keyed by the offset of each JUMPDEST instruction, and the value
 *   is the index of the instruction in the list above
 * @throws std::invalid argument if
 * - parsing an opcode would result in reading out of bounds code
 * - the `immediate_size` member of an instruction would lead to overrunning
 *   a bytes32_t
 * @note this will convert any unknown opcode to the designated OP_INVALID
 * instruction
 */
auto tokenize_code(byte_string_view code)
    -> std::pair<std::vector<Instruction>, JumpDestinations>;

/**
 * Breaks a sequence of instructions into a series of basic blocks where a basic
 * block is defined as a straight-line code sequence with no branches in except
 * to the entry and no branches out except at the exit. Does basic control flow
 * analysis to determine edges between basic blocks.
 * @param instructions
 * @return a map keyed by the index of the basic block that corresponds to
 * `instructions`
 */
[[nodiscard]] auto construct_control_flow_graph(
    InstructionsView instructions, JumpDestinations const &)
    -> ControlFlowGraph;

/**
 * @return a new control flow graph where unreachable blocks are removed
 */
[[nodiscard]] auto prune_unreachable_blocks(ControlFlowGraph)
    -> ControlFlowGraph;

struct BoostGraphVertex
{
    bool operator==(BoostGraphVertex const &other) const = default;
    size_t id;
    BasicBlock const *basic_block;
};

template <typename Vertex>
using BoostGraph = boost::adjacency_list<
    boost::vecS, boost::vecS, boost::bidirectionalS, Vertex>;
using BoostControlFlowGraph = BoostGraph<BoostGraphVertex>;

[[nodiscard]] auto construct_boost_graph(ControlFlowGraph const &graph)
    -> BoostControlFlowGraph;

/**
 * Convenience function that tokenizes a bytecode sequence and parses it into a
 * control flow graph.
 * @param code
 * @return a control flow graph
 */
[[nodiscard]] auto parse_contract(byte_string_view code) -> ControlFlowGraph;

MONAD_ANALYSIS_NAMESPACE_END

template <>
struct fmt::formatter<monad::analysis::Instruction>
    : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(
        monad::analysis::Instruction const &instruction,
        FormatContext &ctx) const
    {
        auto const *instruction_name =
            evmone::instr::traits[instruction.opcode].name;
        constexpr auto remove_leading_zeros = [](std::string_view input) {
            size_t first_non_zero = 0;
            if (input.starts_with("0x")) {
                input.remove_prefix(2);
            }
            while (first_non_zero < input.size() &&
                   input[first_non_zero] == '0') {
                first_non_zero++;
            }
            auto const trimmed = input.substr(first_non_zero);
            if (trimmed.empty()) {
                return fmt::format(" 0x00");
            }
            return fmt::format(" 0x{}", trimmed);
        };
        return fmt::format_to(
            ctx.out(),
            "0x{:02x} {}{}",
            instruction.offset,
            instruction_name != nullptr ? instruction_name : "null",
            (instruction.opcode >= evmone::Opcode::OP_PUSH0 &&
             instruction.opcode <= evmone::Opcode::OP_PUSH32)
                ? remove_leading_zeros(fmt::format("{}", instruction.data))
                : "");
    }
};
