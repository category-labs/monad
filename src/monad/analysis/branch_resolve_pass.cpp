#include <monad/analysis/analysis_fmt.hpp>
#include <monad/analysis/branch_resolve_pass.hpp>
#include <monad/analysis/write_graphviz.hpp>
#include <monad/core/assert.h>

#include <deque>

MONAD_ANALYSIS_NAMESPACE_BEGIN

#define ANY_PUSH                                                               \
    OP_PUSH0:                                                                  \
    case OP_PUSH1:                                                             \
    case OP_PUSH2:                                                             \
    case OP_PUSH3:                                                             \
    case OP_PUSH4:                                                             \
    case OP_PUSH5:                                                             \
    case OP_PUSH6:                                                             \
    case OP_PUSH7:                                                             \
    case OP_PUSH8:                                                             \
    case OP_PUSH10:                                                            \
    case OP_PUSH11:                                                            \
    case OP_PUSH12:                                                            \
    case OP_PUSH13:                                                            \
    case OP_PUSH14:                                                            \
    case OP_PUSH15:                                                            \
    case OP_PUSH16:                                                            \
    case OP_PUSH17:                                                            \
    case OP_PUSH18:                                                            \
    case OP_PUSH19:                                                            \
    case OP_PUSH20:                                                            \
    case OP_PUSH21:                                                            \
    case OP_PUSH22:                                                            \
    case OP_PUSH23:                                                            \
    case OP_PUSH24:                                                            \
    case OP_PUSH25:                                                            \
    case OP_PUSH26:                                                            \
    case OP_PUSH27:                                                            \
    case OP_PUSH28:                                                            \
    case OP_PUSH29:                                                            \
    case OP_PUSH30:                                                            \
    case OP_PUSH31:                                                            \
    case OP_PUSH32

#define ANY_DUP                                                                \
    OP_DUP1:                                                                   \
    case OP_DUP2:                                                              \
    case OP_DUP3:                                                              \
    case OP_DUP4:                                                              \
    case OP_DUP5:                                                              \
    case OP_DUP6:                                                              \
    case OP_DUP7:                                                              \
    case OP_DUP8:                                                              \
    case OP_DUP9:                                                              \
    case OP_DUP10:                                                             \
    case OP_DUP11:                                                             \
    case OP_DUP12:                                                             \
    case OP_DUP13:                                                             \
    case OP_DUP14:                                                             \
    case OP_DUP15:                                                             \
    case OP_DUP16

#define ANY_SWAP                                                               \
    OP_SWAP1:                                                                  \
    case OP_SWAP2:                                                             \
    case OP_SWAP3:                                                             \
    case OP_SWAP4:                                                             \
    case OP_SWAP5:                                                             \
    case OP_SWAP6:                                                             \
    case OP_SWAP7:                                                             \
    case OP_SWAP8:                                                             \
    case OP_SWAP9:                                                             \
    case OP_SWAP10:                                                            \
    case OP_SWAP11:                                                            \
    case OP_SWAP12:                                                            \
    case OP_SWAP13:                                                            \
    case OP_SWAP14:                                                            \
    case OP_SWAP15:                                                            \
    case OP_SWAP16

ANONYMOUS_NAMESPACE_BEGIN

using Stack = std::vector<std::optional<bytes32_t>>;

template <typename TCallable>
void do_binary_operation(Stack &stack, TCallable &&f)
{

    auto maybe_a = stack.at(stack.size() - 1);
    auto maybe_b = stack.at(stack.size() - 2);

    stack.pop_back();
    stack.pop_back();
    if (!maybe_a.has_value() || !maybe_b.has_value()) {
        stack.push_back(std::nullopt);
    }
    else {

        auto a = intx::be::load<monad::uint256_t>(maybe_a.value());
        auto b = intx::be::load<monad::uint256_t>(maybe_b.value());

        auto const result = f(a, b);

        monad::bytes32_t data = intx::be::store<monad::bytes32_t>(result);

        stack.push_back(data);
    }
}

template <typename TCallable>
void do_binary_predicate(Stack &stack, TCallable &&f)
{

    auto maybe_a = stack.at(stack.size() - 1);
    auto maybe_b = stack.at(stack.size() - 2);

    stack.pop_back();
    stack.pop_back();
    if (!maybe_a.has_value() || !maybe_b.has_value()) {
        stack.push_back(std::nullopt);
    }
    else {

        auto a = intx::be::load<monad::uint256_t>(maybe_a.value());
        auto b = intx::be::load<monad::uint256_t>(maybe_b.value());

        bool const result = f(a, b);

        if (result) {
            stack.push_back(0x00000000000000000000000000000001_bytes32);
        }
        else {
            stack.push_back(0x00000000000000000000000000000000_bytes32);
        }
    }
}

void do_not(Stack &stack)
{
    auto maybe_a = stack.at(stack.size() - 1);
    stack.pop_back();
    if (!maybe_a.has_value()) {
        stack.push_back(std::nullopt);
        return;
    }
    auto a = intx::be::load<monad::uint256_t>(maybe_a.value());
    auto result = ~a;
    monad::bytes32_t data = intx::be::store<monad::bytes32_t>(result);
    stack.push_back(data);
}

void do_is_zero(Stack &stack)
{
    auto maybe_a = stack.at(stack.size() - 1);

    stack.pop_back();
    if (!maybe_a.has_value()) {
        stack.push_back(std::nullopt);
        return;
    }
    auto a = intx::be::load<uint256_t>(maybe_a.value());

    if (a == uint256_t{0}) {
        stack.push_back(0x00000000000000000000000000000001_bytes32);
    }
    else {
        stack.push_back(0x00000000000000000000000000000000_bytes32);
    }
}

using BinaryOp = uint256_t(uint256_t const &a, uint256_t const &b);
using BinaryPredicate = bool(uint256_t const &a, uint256_t const &b);

using enum evmone::Opcode;
std::unordered_map<evmone::Opcode, BinaryOp *> binop_handlers = {
    {OP_AND, [](auto const &a, auto const &b) { return a & b; }},
    {OP_SHR, [](auto const &a, auto const &b) { return a >> b; }},
    {OP_SHL, [](auto const &a, auto const &b) { return a << b; }},
    {OP_ADD, [](auto const &a, auto const &b) { return a + b; }},
    {
        OP_EXP,
        [](auto const &a, auto const &b) { return intx::exp(a, b); },
    },
    {OP_SUB, [](auto const &a, auto const &b) { return a - b; }},
    {OP_MUL, [](auto const &a, auto const &b) { return a * b; }},
    {OP_DIV, [](auto const &a, auto const &b) { return a / b; }},
    {OP_OR, [](auto const &a, auto const &b) { return a | b; }},
};

std::unordered_map<evmone::Opcode, BinaryPredicate *>
    binary_predicate_handlers = {
        {OP_EQ, [](auto const &a, auto const &b) { return a == b; }},
        {OP_LT, [](auto const &a, auto const &b) { return a < b; }},
        {OP_GT, [](auto const &a, auto const &b) { return a > b; }},
};

void simulate_opcode(
    std::vector<std::optional<bytes32_t>> &stack,
    Instruction const &instruction)
{
    using enum evmone::Opcode;
    auto const &instruction_info = evmone::instr::traits[instruction.opcode];

    switch (instruction.opcode) {
    case OP_POP:
    case OP_CALLDATACOPY:
    case OP_RETURNDATACOPY:
    case OP_MSTORE: {
        for (int i = 0; i < instruction_info.stack_height_required; i++) {
            stack.pop_back();
        }
        break;
    }
    case OP_AND:
    case OP_SHR:
    case OP_SHL:
    case OP_ADD:
    case OP_EXP:
    case OP_SUB:
    case OP_MUL:
    case OP_DIV:
    case OP_OR: {
        do_binary_operation(stack, binop_handlers.at(instruction.opcode));
        break;
    }

    case OP_EQ:
    case OP_LT:
    case OP_GT: {
        do_binary_predicate(
            stack, binary_predicate_handlers.at(instruction.opcode));
        break;
    }

    case OP_NOT: {
        do_not(stack);
        break;
    }

    case OP_ISZERO: {
        do_is_zero(stack);
        break;
    }

    case OP_CALLDATALOAD:
    case OP_EXTCODESIZE:
    case OP_CALLVALUE:
    case OP_TIMESTAMP:
    case OP_CALLER:
    case OP_ADDRESS:
    case OP_GAS:
    case OP_CALLDATASIZE:
    case OP_RETURNDATASIZE:
    case OP_SLOAD:
    case OP_MLOAD:
    case OP_KECCAK256:
    case OP_STATICCALL:
    case OP_CALL: {
        for (int i = 0; i < instruction_info.stack_height_required; i++) {
            stack.pop_back();
        }

        stack.push_back(std::nullopt);
        break;
    }
    case OP_JUMPDEST:
    case OP_JUMP:
    case OP_JUMPI: {
        for (int i = 0; i < instruction_info.stack_height_required; i++) {
            stack.pop_back();
        }
        break;
    }
    case ANY_PUSH: {
        stack.push_back(instruction.data);
        break;
    }
    case ANY_SWAP: {
        auto const swap_offset = instruction_info.stack_height_required - 1;
        MONAD_ASSERT(swap_offset > 0);

        auto const signed_swap_offset = static_cast<size_t>(swap_offset);

        std::swap(
            stack.at(stack.size() - 1),
            stack.at(stack.size() - signed_swap_offset - 1));
        break;
    }
    case ANY_DUP: {
        auto const dup_offset = instruction_info.stack_height_required;
        MONAD_ASSERT(dup_offset > 0);
        auto const signed_dup_offset = static_cast<size_t>(dup_offset);
        stack.push_back(stack.at(stack.size() - signed_dup_offset));
        break;
    }

    default:
        throw std::runtime_error(
            fmt::format("unimplemented opcode {}", instruction));
    }
}

auto advanced_resolve_jump(
    BoostControlFlowGraph const &graph,
    std::deque<BoostControlFlowGraph::vertex_descriptor> const &path,
    JumpDestinations const &jump_destinations)
    -> std::optional<ResolvedControlFlow>
{
    std::vector<Instruction const *> instructions;

    int min_height_required = 0;
    for (auto const &vertex_descriptor : path) {
        auto const &[block_id, basic_block] = graph[vertex_descriptor];
        for (auto const &instruction : basic_block->get_instructions()) {
            min_height_required +=
                evmone::instr::traits[instruction.opcode].stack_height_required;
            instructions.push_back(&instruction);
        }
    }

    MONAD_DEBUG_ASSERT(min_height_required > 0);
    std::vector<std::optional<bytes32_t>> stack{
        static_cast<size_t>(min_height_required), std::nullopt};

    for (auto it = instructions.cbegin(); it != instructions.cend(); it++) {
        if (std::next(it) == instructions.cend()) {
            break;
        }

        auto const *instruction = *it;
        auto const &instruction_info =
            evmone::instr::traits[instruction->opcode];
        auto const height_required = instruction_info.stack_height_required;

        MONAD_DEBUG_ASSERT(
            std::cmp_greater_equal(stack.size(), height_required));

        auto const stack_size_before = static_cast<int>(stack.size());
        simulate_opcode(stack, *instruction);
        auto const stack_size_after = static_cast<int>(stack.size());

        MONAD_DEBUG_ASSERT(
            stack_size_after - stack_size_before ==
            instruction_info.stack_height_change);
    }

    if (stack.empty()) {
        return std::nullopt;
    }

    MONAD_DEBUG_ASSERT(
        !graph[path.back()].basic_block->is_control_flow_resolved());

    auto const unresolved_control_flow = std::get<UnresolvedControlFlow>(
        graph[path.back()].basic_block->get_control_flow());

    if (stack.at(stack.size() - 1).has_value()) {
        auto value = stack.at(stack.size() - 1).value();
        if (jump_destinations.contains(value)) {
            if (std::holds_alternative<UnresolvedStatic>(
                    unresolved_control_flow)) {
                return ResolvedControlFlow{
                    ResolvedStatic{jump_destinations.at(value)}};
            }
            if (std::holds_alternative<UnresolvedDynamic>(
                    unresolved_control_flow)) {
                auto const unresolved_dynamic =
                    std::get<UnresolvedDynamic>(unresolved_control_flow);
                return ResolvedControlFlow{ResolvedDynamic{
                    jump_destinations.at(value),
                    unresolved_dynamic.get_next_basic_block()}};
            }
            std::unreachable();
        }
    }

    return std::nullopt;
}

/**
 * Run Dijkstra's on `graph` using a specific source node `source`.
 * @param graph
 * @param source
 * @return DistanceAndPredecessors
 */
auto dijkstra_with_source(
    BoostControlFlowGraph const &graph,
    BoostControlFlowGraph::vertex_descriptor source_vertex_descriptor)
    -> DistanceAndPredecessors
{
    using namespace boost;

    auto distances = std::vector<int>(boost::num_vertices(graph));
    auto predecessors = std::vector<BoostControlFlowGraph::vertex_descriptor>(
        boost::num_vertices(graph));

    dijkstra_shortest_paths(
        graph,
        source_vertex_descriptor,
        predecessor_map(make_iterator_property_map(
                            predecessors.begin(), get(vertex_index, graph)))
            .distance_map(make_iterator_property_map(
                distances.begin(), get(vertex_index, graph))));

    return DistanceAndPredecessors{
        .distances = std::move(distances),
        .predecessors = std::move(predecessors)};
}

/**
 * @param graph
 * @param source
 * @return List of every basic block reachable from `source` whose control flow
 * is unresolved along with the `DistanceAndPredecessors` data computed by
 * running Dijkstra's.
 */
auto get_unresolved_blocks_reachable_from(
    BoostControlFlowGraph const &graph,
    BoostControlFlowGraph::vertex_descriptor source)
    -> std::pair<
        std::vector<BoostControlFlowGraph::vertex_descriptor>,
        DistanceAndPredecessors const>
{
    auto dijkstra_result = dijkstra_with_source(graph, source);

    std::vector<BoostControlFlowGraph::vertex_descriptor>
        reachable_unresolved_vertices;

    for (auto [vertex_it, vertex_end] = boost::vertices(graph);
         vertex_it != vertex_end;
         vertex_it++) {
        if (dijkstra_result.distances[*vertex_it] !=
                std::numeric_limits<int>::max() &&
            !graph[*vertex_it].basic_block->is_control_flow_resolved()) {
            reachable_unresolved_vertices.push_back(*vertex_it);
        }
    }

    return std::make_pair(
        std::move(reachable_unresolved_vertices), std::move(dijkstra_result));
}

template <typename TGraph>
void write_graph_to_file(TGraph const &graph, std::string name)
{
    std::ofstream f{name};

    if constexpr (std::is_same_v<ControlFlowGraph, TGraph>) {
        auto const boost_graph = construct_boost_graph(graph);
        write_graphviz(f, boost_graph);
    }
    else if constexpr (std::is_same_v<BoostControlFlowGraph, TGraph>) {
        write_graphviz(f, graph);
    }
    else {
        static_assert(false);
    }
}

// #define GRAPH_DEBUG

/**
 * Branch resolve pass subroutine. Attempt to resolve currently unresolved basic
 * blocks in `graph` by finding a path from a node with no incident edges to the
 * unresolved block, and replaying all the stack operations up until the
 * unresolved control flow instruction.
 * @param graph
 * @param boost_graph
 * @param source
 * @param jump_destinations
 * @return the updated control flow graph
 */
auto branch_resolve_pass_reachable_from(
    ControlFlowGraph graph, BoostControlFlowGraph const &boost_graph,
    BoostControlFlowGraph::vertex_descriptor const source,
    JumpDestinations const &jump_destinations)
    -> std::pair<size_t, ControlFlowGraph>
{
    if (graph.empty()) {
        return {0, std::move(graph)};
    }

    auto const [reachable_unresolved_blocks, dijkstra_result] =
        get_unresolved_blocks_reachable_from(boost_graph, source);

    size_t newly_resolved_blocks = 0;
    for (auto const &reachable_unresolved_block : reachable_unresolved_blocks) {
        std::deque<BoostControlFlowGraph::vertex_descriptor> path;
        auto traverse = reachable_unresolved_block;
        path.push_front(traverse);

        while (traverse != dijkstra_result.predecessors[traverse]) {
            traverse = dijkstra_result.predecessors[traverse];
            path.push_front(traverse);
        }

#ifdef GRAPH_DEBUG
        if (path.size() > 1) {
            auto name = fmt::format(
                "bb_{}_to_bb_{}.dot",
                boost_graph[path.front()].id,
                boost_graph[path.back()].id);

            BoostControlFlowGraph path_graph;

            std::vector<BoostControlFlowGraph::vertex_descriptor> vds;
            for (auto const &vd : path) {
                vds.push_back(boost::add_vertex(
                    BoostGraphVertex{
                        boost_graph[vd].id, boost_graph[vd].basic_block},
                    path_graph));
            }

            for (size_t i = 0; i < vds.size() - 1; i++) {
                boost::add_edge(vds[i], vds[i + 1], path_graph);
            }

            write_graph_to_file(path_graph, name);
        }
#endif

        auto maybe_resolved_jump =
            advanced_resolve_jump(boost_graph, path, jump_destinations);

        if (maybe_resolved_jump.has_value()) {
            newly_resolved_blocks++;
            graph.at(boost_graph[reachable_unresolved_block].id)
                .set_control_flow(ControlFlow{maybe_resolved_jump.value()});
        }
    }

    return {newly_resolved_blocks, std::move(graph)};
}
ANONYMOUS_NAMESPACE_END

auto branch_resolve_pass(
    ControlFlowGraph graph, JumpDestinations const &jump_destinations)
    -> std::pair<size_t, ControlFlowGraph>
{
    size_t num_resolved_branches = 0;
    while (true) {
        std::vector<BoostControlFlowGraph::vertex_descriptor> source_nodes;

        auto boost_graph = construct_boost_graph(graph);

        for (auto [it, end] = boost::vertices(boost_graph); it != end; it++) {
            if (boost::in_degree(*it, boost_graph) == 0) {
                source_nodes.push_back(*it);
            }
        }

        bool exit = true;
        for (auto const &source : source_nodes) {
            auto [newly_resolved_branches, new_graph] =
                branch_resolve_pass_reachable_from(
                    std::move(graph), boost_graph, source, jump_destinations);

            graph = std::move(new_graph);
            if (newly_resolved_branches != 0) {
                num_resolved_branches += newly_resolved_branches;
                exit = false;
            }
        }

        if (exit) {
            break;
        }
    }

    return std::make_pair(num_resolved_branches, std::move(graph));
}

MONAD_ANALYSIS_NAMESPACE_END
