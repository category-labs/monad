#pragma once

#include <monad/analysis/analysis.hpp>
#include <monad/core/basic_formatter.hpp>

#include <boost/graph/graphviz.hpp>

#include <ostream>

MONAD_ANALYSIS_NAMESPACE_BEGIN

class VertexWriter
{
public:
    explicit VertexWriter(BoostControlFlowGraph const &graph);

    void operator()(
        std::ostream &out,
        BoostControlFlowGraph::vertex_descriptor const &vertex_descriptor)
        const noexcept;

private:
    BoostControlFlowGraph const &graph_;
};

void write_graphviz(std::ostream &ostream, BoostControlFlowGraph const &graph);

MONAD_ANALYSIS_NAMESPACE_END
