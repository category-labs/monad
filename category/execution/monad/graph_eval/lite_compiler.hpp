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

#include "category/core/assert.h"
#include <category/core/result.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

struct Lifetime;
struct Lowering;

class LiteCompiledGraph
{
    friend struct Lowering;

    std::vector<uint8_t> kernel_blob_;
    // TODO: beware, this may have the wrong alignment.
    std::vector<uint8_t> data_blob_;
    std::vector<uint32_t> input_offsets_;
    std::vector<uint32_t> output_offsets_;

public:
    std::vector<uint32_t> const &input_offsets() const
    {
        return input_offsets_;
    }

    std::vector<uint32_t> const &output_offsets() const
    {
        return output_offsets_;
    }

    // Morally const, but we provide data_blob_ as part of the
    // arenas array, which mixes up read-only and read-write areas
    // run assumes inputs have been written at input_offsets() by
    // the caller
    Result<void> run(std::span<uint8_t> scratch);
};

enum class Arena : uint8_t
{
    Memory,
    Literals,
    Region,
    Last_valid = Region,
    Invalid
};

// Arena 0 = general-purpose memory
// Arena 1 = literals pool
// Arena 2 = per-region scratchpad
using kernel_memory_arenas =
    std::array<uint8_t *, 1 + static_cast<size_t>(Arena::Last_valid)>;

struct Place
{
    Arena arena = Arena::Invalid;
    uint32_t offset = 0;

    template <typename T>
    T *get_as(kernel_memory_arenas &arenas)
    {
        MONAD_DEBUG_ASSERT(arena != Arena::Invalid);
        return reinterpret_cast<T *>(
            arenas[static_cast<size_t>(arena)] + offset);
    }
};

class LiteCompiler
{
    friend struct Lowering;

    Graphcode const &gc_;
    std::span<uint8_t const> code_;
    State &state_; // For fetching TensorRef nodes

    // The compiler loads the entire graphcode into memory
    // TODO: use a better representation than the huge variant
    size_t n_inputs_ = 0;

    // Beware the ops_ vector only contains ops (no inputs) but all the other
    // vectors do account for inputs. TODO: do something better.
    std::vector<AnyGraphOp> ops_;
    std::vector<size_t> users_;
    std::vector<TensorType> node_types_;
    std::vector<size_t> outputs_;
    std::vector<Place> node_placements_;
    std::vector<Lifetime> lifetimes_;
    size_t arena_size_ = 0;

    Result<void> read_graphcode();
    Result<void> allocate_nodes();
    Result<LiteCompiledGraph> lower();

    LiteCompiler(Graphcode const &gc, State &state);

public:
    static Result<LiteCompiledGraph> compile(Graphcode const &gc, State &state);

    LiteCompiler(LiteCompiler const &) = delete;
    LiteCompiler(LiteCompiler &&) = delete;
    LiteCompiler &operator=(LiteCompiler const &) = delete;
    LiteCompiler &operator=(LiteCompiler &&) = delete;
};

MONAD_GRAPH_EVAL_NAMESPACE_END
