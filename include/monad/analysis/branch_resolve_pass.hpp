#pragma once

#include <monad/analysis/analysis.hpp>

MONAD_ANALYSIS_NAMESPACE_BEGIN

/**
 * Helper struct containing data returned by Boost.Graph's implementation of
 * Dijkstra's.
 */
struct DistanceAndPredecessors
{
    std::vector<int> distances;
    std::vector<BoostControlFlowGraph::vertex_descriptor> predecessors;
};

/**
 * Repeatedly attempts to resolve branches until no new branches are resolved.
 * @param graph
 * @param jump_destinations
 * @return the updated control flow graph
 */
auto branch_resolve_pass(
    ControlFlowGraph graph, JumpDestinations const &jump_destinations)
    -> std::pair<size_t, ControlFlowGraph>;

MONAD_ANALYSIS_NAMESPACE_END
