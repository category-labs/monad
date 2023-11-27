#include <monad/analysis/analysis.hpp>
#include <monad/analysis/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/core/variant.hpp>

#include <evmone/instructions_opcodes.hpp>
#include <evmone/instructions_traits.hpp>

#include <boost/graph/detail/adjacency_list.hpp>

#include <algorithm>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <format>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

MONAD_ANALYSIS_NAMESPACE_BEGIN

Instruction::Instruction(evmone::Opcode opcode)
    : offset{}
    , opcode{opcode}
    , data{}
{
}

Instruction::Instruction(evmone::Opcode opcode, bytes32_t data)
    : offset{}
    , opcode{opcode}
    , data{data}
{
}

Instruction::Instruction(size_t offset, evmone::Opcode opcode, bytes32_t data)
    : offset{offset}
    , opcode{opcode}
    , data{data}
{
}

Instruction::Instruction(size_t offset, evmone::Opcode opcode)
    : Instruction{offset, opcode, 0x00_bytes32}
{
}

bool Instruction::operator==(Instruction const &rhs) const
{
    return opcode == rhs.opcode && data == rhs.data;
}

bool Instruction::operator!=(Instruction const &rhs) const
{
    return !(rhs == *this);
}

ResolvedStatic::ResolvedStatic(size_t target)
    : target_{target}
{
}

size_t ResolvedStatic::get_target() const
{
    return target_;
}

UnresolvedDynamic::UnresolvedDynamic(size_t next_basic_block)
    : next_basic_block_{next_basic_block}
{
}

size_t UnresolvedDynamic::get_next_basic_block() const
{
    return next_basic_block_;
}

ResolvedDynamic::ResolvedDynamic(size_t taken_target, size_t not_taken_target)
    : taken_target_{taken_target}
    , not_taken_target_{not_taken_target}
{
}

size_t ResolvedDynamic::get_taken_target() const
{
    return taken_target_;
}

size_t ResolvedDynamic::get_not_taken_target() const
{
    return not_taken_target_;
}

Linear::Linear(size_t next_basic_block)
    : next_basic_block_{next_basic_block}
{
}

size_t Linear::get_next_basic_block() const
{
    return next_basic_block_;
}

BasicBlock::BasicBlock(InstructionsView instructions, ControlFlow control_flow)
    : instructions_{instructions.begin(), instructions.end()}
    , control_flow_{control_flow}
{
}

Instructions const &BasicBlock::get_instructions() const
{
    return instructions_;
}

ControlFlow const &BasicBlock::get_control_flow() const
{
    return control_flow_;
}

std::optional<size_t> BasicBlock::get_indirect_branch() const
{
    using Return = std::optional<size_t>;
    return std::visit(
        overloaded{
            [](ResolvedControlFlow const &resolved) -> Return {
                return std::visit(
                    overloaded{
                        [](ResolvedDynamic const &resolved_dynamic) -> Return {
                            return resolved_dynamic.get_taken_target();
                        },
                        [](auto) -> Return { return std::nullopt; }},
                    resolved);
            },
            [](auto) -> Return { return std::nullopt; }},
        control_flow_);
}

std::optional<size_t> BasicBlock::get_next_basic_block() const
{
    using Return = std::optional<size_t>;
    return std::visit(
        overloaded{
            [](ResolvedControlFlow const &resolved) -> Return {
                return std::visit(
                    overloaded{
                        [](Linear const &linear) -> Return {
                            return linear.get_next_basic_block();
                        },
                        [](ResolvedStatic const &resolved_static) -> Return {
                            return resolved_static.get_target();
                        },
                        [](ResolvedDynamic const &resolved_dynamic) -> Return {
                            return resolved_dynamic.get_not_taken_target();
                        },
                        [](Halting const &) -> Return { return std::nullopt; }},
                    resolved);
            },
            [](UnresolvedControlFlow const &unresolved) -> Return {
                return std::visit(
                    overloaded{
                        [](UnresolvedDynamic const &unresolved_dynamic)
                            -> Return {
                            return unresolved_dynamic.get_next_basic_block();
                        },
                        [](UnresolvedStatic const &) -> Return {
                            return std::nullopt;
                        }},
                    unresolved);
            }},
        control_flow_);
}

bool BasicBlock::is_control_flow_resolved() const
{
    return std::holds_alternative<ResolvedControlFlow>(control_flow_);
}

namespace
{
    constexpr bool is_push(evmone::Opcode opcode)
    {
        return opcode >= evmone::Opcode::OP_PUSH0 &&
               opcode <= evmone::Opcode::OP_PUSH32;
    }

    std::optional<size_t> resolve_jump(
        InstructionsView const instructions, size_t index,
        JumpDestinations const &jump_destinations)
    {
        if (instructions.empty() || index == 0 ||
            index >= instructions.size()) {
            return std::nullopt;
        }

        auto const &previous_instruction = instructions[index - 1];

        if (!is_push(previous_instruction.opcode)) {
            return std::nullopt;
        }

        if (!jump_destinations.contains(previous_instruction.data)) {
            return std::nullopt;
        }

        return jump_destinations.at(previous_instruction.data);
    }

    ControlFlow get_control_flow_for_jump(
        evmone::Opcode opcode, InstructionsView const &instructions,
        size_t instruction_index, JumpDestinations const &jump_destinations)
    {
        using enum evmone::Opcode;
        MONAD_DEBUG_ASSERT(opcode == OP_JUMP || opcode == OP_JUMPI);
        bool const is_last = instruction_index + 1 >= instructions.size();
        if (auto maybe_jump_index = resolve_jump(
                instructions, instruction_index, jump_destinations);
            maybe_jump_index.has_value()) {
            auto jump_index = maybe_jump_index.value();
            if (opcode == OP_JUMPI) {
                if (!is_last) {
                    return ResolvedControlFlow{
                        ResolvedDynamic{jump_index, instruction_index + 1}};
                }
                return ResolvedControlFlow{ResolvedStatic{jump_index}};
            }
            if (opcode == OP_JUMP) {
                return ResolvedControlFlow{ResolvedStatic{jump_index}};
            }
            std::unreachable();
        }
        else {
            if (opcode == OP_JUMPI) {
                if (!is_last) {
                    return UnresolvedControlFlow{
                        UnresolvedDynamic{instruction_index + 1}};
                }
                return UnresolvedControlFlow{UnresolvedStatic{}};
            }
            if (opcode == OP_JUMP) {
                return UnresolvedControlFlow{UnresolvedStatic{}};
            }
            std::unreachable();
        }
    }
}

auto pad_code(byte_string code) -> byte_string
{
    using OpcodeType = std::underlying_type_t<evmone::Opcode>;
    static_assert(std::is_same_v<OpcodeType, uint8_t>);
    // We need at most 33 bytes of code padding: 32 for possible missing all
    // data bytes of PUSH32 at the very end of the code; and one more byte for
    // STOP to guarantee there is a terminating instruction at the code end.
    constexpr auto padding = 32 + 1;

    byte_string padded_code{std::move(code)};
    padded_code.reserve(padding);

    for (auto i = 0; i < padding; i++) {
        padded_code += static_cast<OpcodeType>(evmone::Opcode::OP_STOP);
    }

    return padded_code;
}

auto tokenize_code(byte_string_view code)
    -> std::pair<std::vector<Instruction>, JumpDestinations>
{
    JumpDestinations jump_destinations;

    std::vector<Instruction> tokens;
    tokens.reserve(code.size());

    auto const *code_start = code.data();

    while (!code.empty()) {
        auto const opcode = *code.begin();
        auto const offset = code.data() - code_start;
        auto const instruction = ::evmone::instr::traits[opcode];
        auto const *instruction_name =
            (instruction.name == nullptr) ? "null" : instruction.name;
        auto const immediate_size = instruction.immediate_size;

        // parse any unknown opcode as OP_INVALID and move on
        if (MONAD_UNLIKELY(instruction.name == nullptr)) {
            tokens.emplace_back(
                offset, evmone::Opcode::OP_INVALID, bytes32_t{});
            code.remove_prefix(1);
            continue;
        }

        if (MONAD_UNLIKELY(std::cmp_less(code.size(), immediate_size + 1))) {
            throw std::invalid_argument{std::format(
                "parsing opcode {} at code offset {} would read past code "
                "view",
                instruction_name,
                offset)};
        }

        if (MONAD_UNLIKELY(immediate_size > sizeof(bytes32_t))) {
            throw std::invalid_argument{std::format(
                "parsing immediate size {} operand for opcode {} at code "
                "offset {} would overflow bytes32_t",
                immediate_size,
                instruction_name,
                offset)};
        }

        if (opcode == evmone::Opcode::OP_JUMPDEST) {
            jump_destinations.emplace(offset, tokens.size());
        }

        // consume opcode
        code.remove_prefix(1);

        bytes32_t data{0};

        // on a big-endian arch, std::copy_n would suffice
        static_assert(std::endian::native == std::endian::little);
        std::copy_backward(
            code.data(),
            code.data() + immediate_size,
            data.bytes + sizeof(data));

        tokens.emplace_back(offset, evmone::Opcode{opcode}, data);

        // consume immediate, if any
        code.remove_prefix(immediate_size);
    }

    return std::make_pair(std::move(tokens), std::move(jump_destinations));
}

auto construct_control_flow_graph(
    InstructionsView const instructions,
    JumpDestinations const &jump_destinations) -> ControlFlowGraph
{
    if (instructions.empty()) {
        return {};
    }

    ControlFlowGraph control_flow_graph;

    std::deque<size_t> blocks_to_visit;
    blocks_to_visit.emplace_back(0);

    while (!blocks_to_visit.empty()) {
        using enum evmone::Opcode;
        auto const start = blocks_to_visit.front();
        auto instruction_index = start;

        std::optional<ControlFlow> control_flow;
        while (instruction_index < instructions.size()) {
            auto const opcode = instructions[instruction_index].opcode;

            if (opcode == OP_JUMP || opcode == OP_JUMPI) {
                control_flow = get_control_flow_for_jump(
                    opcode, instructions, instruction_index, jump_destinations);
                break;
            }

            if (opcode == OP_STOP || opcode == OP_REVERT ||
                opcode == OP_SELFDESTRUCT || opcode == OP_RETURN ||
                opcode == OP_INVALID) {
                control_flow = ControlFlow{ResolvedControlFlow{Halting{}}};
                break;
            }

            if (opcode == OP_JUMPDEST && instruction_index != start) {
                control_flow =
                    ControlFlow{ResolvedControlFlow{Linear{instruction_index}}};
                instruction_index--;
                break;
            }

            instruction_index++;
        }

        if (instruction_index == instructions.size()) {
            break;
        }

        MONAD_DEBUG_ASSERT(control_flow.has_value());
        BasicBlock block{
            instructions.subspan(start, instruction_index - start + 1),
            control_flow.value()};

        control_flow_graph.emplace(start, block);

        auto const maybe_indirect_branch = block.get_indirect_branch();
        if (maybe_indirect_branch.has_value() &&
            !control_flow_graph.contains(maybe_indirect_branch.value())) {
            blocks_to_visit.emplace_back(maybe_indirect_branch.value());
        }

        blocks_to_visit.emplace_back(++instruction_index);
        blocks_to_visit.pop_front();
    }

    return control_flow_graph;
}

ControlFlowGraph prune_unreachable_blocks(ControlFlowGraph graph)
{
    if (graph.empty()) {
        return {};
    }

    auto const first_basic_block_index = graph.begin()->first;

    std::unordered_set<size_t> incident_nodes;

    for (auto const &[index, node] : graph) {
        if (auto next_block = node.get_next_basic_block();
            next_block.has_value()) {
            incident_nodes.insert(next_block.value());
        }

        if (auto indirect_branch = node.get_indirect_branch();
            indirect_branch.has_value()) {
            incident_nodes.insert(indirect_branch.value());
        }
    }

    std::vector<size_t> nodes_to_prune;
    for (auto &[index, node] : graph) {
        if (index != first_basic_block_index &&
            !incident_nodes.contains(index) &&
            !node.get_instructions().empty() &&
            node.get_instructions().begin()->opcode !=
                evmone::Opcode::OP_JUMPDEST) {
            nodes_to_prune.emplace_back(index);
        }
    }

    for (auto const &index : nodes_to_prune) {
        graph.erase(index);
    }

    return graph;
}

auto construct_boost_graph(ControlFlowGraph const &control_flow_graph)
    -> BoostControlFlowGraph
{

    auto find_vertex = [](size_t index,
                          BasicBlock const *basic_block,
                          BoostControlFlowGraph const &graph)
        -> std::optional<BoostControlFlowGraph::vertex_descriptor> {
        using vd = BoostControlFlowGraph::vertex_descriptor;
        const auto vip = boost::vertices(graph);
        BoostGraphVertex const vertex{index, basic_block};
        const auto i = std::find_if(
            vip.first, vip.second, [&vertex, &graph](const vd descriptor) {
                return graph[descriptor] == vertex;
            });

        if (i == vip.second) {
            return std::nullopt;
        }

        return std::make_optional(*i);
    };

    BoostControlFlowGraph graph;

    std::vector<BoostControlFlowGraph::vertex_descriptor> vertex_descriptors;
    vertex_descriptors.reserve(control_flow_graph.size());

    for (auto const &[index, node] : control_flow_graph) {
        vertex_descriptors.emplace_back(
            boost::add_vertex(BoostGraphVertex{index, &node}, graph));
    }

    for (auto const &vertex_descriptor : vertex_descriptors) {
        auto const vertex1 = vertex_descriptor;
        auto const &node = *graph[vertex1].basic_block;

        for (auto const &maybe_next_index :
             {node.get_next_basic_block(), node.get_indirect_branch()}) {

            if (maybe_next_index.has_value()) {
                auto const next_index = maybe_next_index.value();
                auto const &next_node = control_flow_graph.at(next_index);
                auto const vertex2 =
                    find_vertex(next_index, &next_node, graph).value();
                boost::add_edge(vertex1, vertex2, graph);
            }
        }
    }

    return graph;
}

auto parse_contract(byte_string_view code) -> ControlFlowGraph
{
    auto const padded_code = pad_code(byte_string{code});
    auto const [instructions, jump_destinations] = tokenize_code(padded_code);
    auto control_flow_graph =
        construct_control_flow_graph(instructions, jump_destinations);
    auto pruned_control_flow_graph =
        prune_unreachable_blocks(std::move(control_flow_graph));
    return pruned_control_flow_graph;
}

MONAD_ANALYSIS_NAMESPACE_END
