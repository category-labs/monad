// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/core/result.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/fuse_claude.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// Fused code, in fuse_claude.hpp's format, interpreted rather than compiled.
// Validation, once per code, accepts and rejects what FusedGraphCompiler does,
// and keeps only what the reference interpreter's Graphcode keeps: each node's
// type and place, and the memory's size. run() then reads the code's ops and
// instructions again on every call: each op's Constants and broadcast loops
// once, then for every chunk it walks the instructions, choosing each one's
// kernel by its operands' dtypes and its chunk buffer as it goes, where
// FusedGraph runs steps planned in advance.
// Everything else is FusedGraph's: the places of the tensors and the chunk
// buffers, the chunks, the order the kernels run in and the kernels
// themselves, so a run leaves the memory as FusedGraph's run of the same code
// does.
class FusedInterpreter
{
    // The code, which the caller keeps alive, and where its ops start
    std::span<uint8_t const> code_;
    size_t ops_offset_ = 0;
    size_t n_ops_ = 0;
    std::vector<TensorType> node_types_;
    // Each node's offset in the memory, and for a node whose core is computed
    // whole, the core's
    std::vector<uint32_t> node_offsets_;
    std::vector<uint32_t> product_offsets_;
    std::vector<uint32_t> input_offsets_;
    std::vector<uint32_t> output_offsets_;
    // The memory holds the tensors, then the chunk buffers
    uint64_t tensors_size_ = 0;
    uint64_t memory_size_ = 0;

    class Validator;

    GraphEvalError run_op(
        std::span<uint8_t const> &code, size_t node, uint8_t *memory,
        State *state) const;

public:
    // Validates `code`, which must outlive the interpreter
    static Result<FusedInterpreter> validate(std::span<uint8_t const> code);

    std::vector<uint32_t> const &input_offsets() const
    {
        return input_offsets_;
    }

    std::vector<uint32_t> const &output_offsets() const
    {
        return output_offsets_;
    }

    uint64_t memory_size() const
    {
        return memory_size_;
    }

    // run assumes inputs have been written at input_offsets() by the caller.
    // A TensorRef core reads its tensor from `state`'s accounts
    Result<void> run(std::span<uint8_t> memory, State *state = nullptr) const;
};

MONAD_GRAPH_EVAL_NAMESPACE_END
