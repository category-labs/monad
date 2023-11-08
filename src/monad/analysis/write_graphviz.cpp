#include <monad/analysis/analysis_fmt.hpp>
#include <monad/analysis/write_graphviz.hpp>

MONAD_ANALYSIS_NAMESPACE_BEGIN

VertexWriter::VertexWriter(BoostControlFlowGraph const &graph)
    : graph_{graph}
{
}

void VertexWriter::operator()(
    std::ostream &out,
    BoostControlFlowGraph::vertex_descriptor const &vd) const noexcept
{
    auto const &node = graph_[vd];
    auto const basic_block_name = std::format("bb_{}", node.id);
    auto const color =
        node.basic_block->is_control_flow_resolved() ? "palegreen" : "orange";
    out << std::format(
        "[fontname=\"Courier "
        "New\",fillcolor=\"{}\",style=\"filled,rounded\",shape=box,label="
        "\"",
        color);
    out << basic_block_name << "\\l";
    if (node.basic_block->get_instructions().empty()) {
        out << "INVALID BASIC BLOCK\\l";
    }
    else {
        out << fmt::format(
            "{}\\lstack height change: {}",
            fmt::join(node.basic_block->get_instructions(), "\\l"),
            node.basic_block->get_stack_height_change());
    }
    out << "\\l\"]";
}

void write_graphviz(std::ostream &ostream, BoostControlFlowGraph const &graph)
{
    boost::write_graphviz(ostream, graph, VertexWriter{graph});
}

MONAD_ANALYSIS_NAMESPACE_END
