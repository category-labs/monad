// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/vm/compiler/ir/poly_typed/infer_state.hpp>

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
