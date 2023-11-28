#pragma once

#include <monad/analysis/analysis.hpp>
#include <monad/analysis/config.hpp>
#include <monad/core/bytes.hpp>

#include <evmone/instructions_opcodes.hpp>

#include <cstddef>
#include <deque>
#include <map>
#include <optional>
#include <unordered_set>
#include <variant>
#include <vector>

MONAD_ANALYSIS_NAMESPACE_BEGIN

struct ConcreteValue
{
    bytes32_t value;
    friend bool
    operator==(ConcreteValue const &, ConcreteValue const &) = default;
};

struct SSABasicBlock;

struct PlaceholderValue
{
    int stack_offset;
    friend bool
    operator==(PlaceholderValue const &, PlaceholderValue const &) = default;
};

struct Register
{
    size_t register_name;
    friend bool operator==(Register const &, Register const &) = default;
};

struct SSAInstruction;

struct StackValue
{
    using Variant = std::variant<ConcreteValue, PlaceholderValue, Register>;
    Variant value;

    SSAInstruction const *writer = nullptr;
    std::unordered_set<SSAInstruction const *> readers;

    explicit StackValue(Variant);
    friend bool operator==(StackValue const &, StackValue const &) = default;
};

using Arguments = std::vector<StackValue>;

struct SSAInstruction
{
    size_t offset;
    evmone::Opcode opcode;
    Arguments arguments;
    std::optional<size_t> return_value;

    friend bool
    operator==(SSAInstruction const &, SSAInstruction const &) = default;
};

using SSAInstructions = std::vector<SSAInstruction>;
using SymbolicStack = std::deque<StackValue>;

struct SSABasicBlock
{
    SSAInstructions const instructions;
    ControlFlow control_flow;
    SymbolicStack stack;

    friend bool
    operator==(SSABasicBlock const &, SSABasicBlock const &) = default;
};

using SSAControlFlowGraph = std::map<size_t, SSABasicBlock>;

[[nodiscard]] SymbolicStack create_prefilled_stack();

[[nodiscard]] bool resolve_phis(SSAControlFlowGraph &control_flow_graph);

[[nodiscard]] bool handle_writers(SSAInstruction const *writer, int depth);

[[nodiscard]] bool
resolve_cross_references(SSAControlFlowGraph &control_flow_graph);

[[nodiscard]] SSAControlFlowGraph
lift_cfg_to_ssa(ControlFlowGraph const &control_flow_graph);

struct BoostSSAGraphVertex
{
    bool operator==(BoostSSAGraphVertex const &other) const = default;
    size_t id;
    SSABasicBlock const *basic_block;
};

using UseDefGraph = BoostGraph<BoostSSAGraphVertex>;
[[nodiscard]] UseDefGraph
construct_use_def_graph(SSAControlFlowGraph const &graph);

MONAD_ANALYSIS_NAMESPACE_END
