#include <category/vm/compiler/ir/poly_typed/infer_state.hpp>
#include <category/vm/compiler/ir/poly_typed/strongly_connected_components.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/core/assert.h>

#include <algorithm>
#include <utility>
#include <vector>

namespace monad::vm::compiler::poly_typed
{
    void strong_connect(TarjanState &state, block_id block)
    {
        std::vector<ConnectBlocks> connect_stack{
            {.block = block, .parent = block, .successors_visited = 0}};

        state.stack.push_back(block);
        auto &block_st = state.vertex_states[block];
        block_st.index = state.index;
        block_st.lowlink = state.index;
        block_st.on_stack = true;
        block_st.is_defined = true;
        ++state.index;

        while (!connect_stack.empty()) {
            auto &b = connect_stack.back();
            auto &bst = state.vertex_states[b.block];

            if (b.successors_visited == bst.successors.size()) {
                auto &pst = state.vertex_states[b.parent];

                if (bst.lowlink == bst.index) {
                    state.components.emplace_back();
                    block_id t;
                    do {
                        t = state.stack.back();
                        state.stack.pop_back();
                        state.components.back().insert(t);
                        state.vertex_states[t].on_stack = false;
                    }
                    while (b.block != t);
                }

                connect_stack.pop_back();

                pst.lowlink = std::min(pst.lowlink, bst.lowlink);
            }
            else {
                MONAD_VM_DEBUG_ASSERT(
                    b.successors_visited < bst.successors.size());
                block_id const s = bst.successors[b.successors_visited];
                ++b.successors_visited;
                auto &sst = state.vertex_states[s];
                if (!sst.is_defined) {
                    connect_stack.push_back(
                        {.block = s,
                         .parent = b.block,
                         .successors_visited = 0});
                    state.stack.push_back(s);
                    sst.index = state.index;
                    sst.lowlink = state.index;
                    sst.on_stack = true;
                    sst.is_defined = true;
                    ++state.index;
                }
                else if (sst.on_stack) {
                    bst.lowlink = std::min(bst.lowlink, sst.index);
                }
            }
        }
    }

    std::vector<Component>
    strongly_connected_components(InferState const &infer_state)
    {
        // Tarjan's algorithm, but without recursive function calls
        TarjanState state{
            .infer_state = infer_state,
            .index = 0,
            .stack = {},
            .vertex_states = {},
            .components = {}};
        for (block_id b = 0; b < infer_state.pre_blocks.size(); ++b) {
            state.vertex_states.emplace_back(
                state.infer_state.static_successors(b), 0, 0, false, false);
        }
        for (block_id b = 0; b < infer_state.pre_blocks.size(); ++b) {
            if (!state.vertex_states[b].is_defined) {
                strong_connect(state, b);
            }
        }
        return std::move(state.components);
    }
}
