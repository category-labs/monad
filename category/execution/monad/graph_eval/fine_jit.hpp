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
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/fine.hpp>
#include <category/execution/monad/graph_eval/interpreter.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <cstdint>
#include <optional>
#include <span>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

class FineJit
{
    Finecode const &finecode_;
    uint8_t const* code_;
    size_t const n_ops_;
    State &state_;
    std::span<TensorInput const> const inputs_;
    CallerStorage *const caller_storage_;
    // The caller's number of output references, if it gave any: run() fails
    // unless the graph has that many outputs
    std::optional<size_t> const output_count_;
    uint8_t *const arena_;

    Tensor node(size_t const id) const;
    Result<void> load_inputs();

    Tensor take_input();

    Result<void> run_scalar(Tensor const out);
public:
    FineJit(
        Finecode const &finecode, State &state,
        std::span<TensorInput const> inputs, CallerStorage *caller_storage,
        std::optional<size_t> output_count, uint8_t *arena)
        : finecode_(finecode)
        , code_(finecode.ops())
        , n_ops_(finecode.n_ops())
        , state_(state)
        , inputs_(inputs)
        , caller_storage_(caller_storage)
        , output_count_(output_count)
        , arena_(arena)
    {
    }

    Result<GraphOutputs> run();
};

MONAD_GRAPH_EVAL_NAMESPACE_END
