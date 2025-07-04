#pragma once

#include <monad/vm/compiler/ir/poly_typed/infer_state.hpp>

namespace monad::vm::compiler::poly_typed
{
    using Component = std::unordered_set<block_id>;

    struct TarjanVertexState
    {
        std::vector<block_id> successors;
        size_t index;
        size_t lowlink;
        bool on_stack;
        bool is_defined;
    };

    struct TarjanState
    {
        InferState const &infer_state;
        size_t index;
        std::vector<block_id> stack;
        std::vector<TarjanVertexState> vertex_states;
        std::vector<Component> components;
    };

    struct ConnectBlocks
    {
        block_id block;
        block_id parent;
        size_t successors_visited;
    };

    void strong_connect(TarjanState &state, block_id block);

    /// Find all the sets of strongly connected components. The LITERAL values
    /// in the LocalStacksIr basic block output defines which basic blocks are
    /// strongly connected. If the output stack of basic block A has the address
    /// of basic block B as a LITERAL in the output stack, then there is an edge
    /// from A to B.
    std::vector<Component>
    strongly_connected_components(InferState const &infer_state);
}
