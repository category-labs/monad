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

#include "category/core/result.hpp"
#include "category/execution/ethereum/state3/state.hpp"
#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/graphcode.hpp"
#include "category/execution/monad/graph_eval/references.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// Evaluates graphcode on inputs as read from the calldata: literals, or
// references to tensors in accounts' code or in the caller's storage
class Interpreter
{
    Graphcode const &graphcode_;
    State &state_;
    std::vector<TensorInput> inputs_;
    // The caller's storage, for storage references, under DELEGATECALL only
    CallerStorage *const caller_storage_;
    // For evalGraphInto, its number of outputs, which must be the graph's
    std::optional<size_t> const output_count_;

    std::span<uint8_t const> code_span_;
    std::vector<Tensor> node_values_;

    uint8_t *const arena_;

    Result<void> check_magic_number();
    Result<void> check_inputs();
    Result<void> load_inputs();
    Result<void> prepare_node_placement();

public:
    Interpreter(
        State &state, std::vector<TensorInput> &&inputs,
        CallerStorage *const caller_storage,
        std::optional<size_t> const output_count, Graphcode const &graphcode,
        uint8_t *const arena)
        : graphcode_(graphcode)
        , state_(state)
        , inputs_(std::move(inputs))
        , caller_storage_(caller_storage)
        , output_count_(output_count)
        , code_span_(graphcode.code(), graphcode.code_size())
        , arena_(arena)
    {
    }

    ~Interpreter() = default;

    Interpreter(Interpreter const &other) = delete;
    Interpreter &operator=(Interpreter const &other) = delete;
    Interpreter(Interpreter &&other) = delete;
    Interpreter &operator=(Interpreter &&other) = delete;

    Result<std::vector<Tensor>> run();
};

// Benchmarking: prints how long each node of the thread's last evaluation took,
// once, if interpreter.cpp's TIME_NODES is set. The evaluation only records
// the times, so that the printing can be done after anything being timed
void print_node_times();

MONAD_GRAPH_EVAL_NAMESPACE_END
