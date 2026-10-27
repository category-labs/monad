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
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graphcode.hpp"
#include "category/execution/monad/graph_eval/references.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// Evaluates graphcode on inputs as read from the calldata: literals, or
// references to tensors in accounts' code or in the caller's storage
// Benchmarking: the time of each part of the runs of the Interpreters given
// it with time_nodes, or the LiteCompiledGraphs given it with time_kernels,
// summed over them, as ticks of the timestamp counter: from the start of run()
// to its first op, each op, and from its last op to the end of run(). An op's
// time includes reading it from the graphcode, or its kernel's record from the
// kernel blob. The runs are expected to be of one graph
class NodeTimes
{
    friend class Interpreter;
    friend class LiteCompiledGraph;

    struct Node
    {
        Op op;
        TensorType type;
        uint64_t ticks;
    };

    uint64_t runs_ = 0;
    uint64_t setup_ = 0;
    uint64_t outputs_ = 0;
    uint64_t total_ = 0;
    // The node id of the first op, after the inputs'
    size_t first_id_ = 0;
    std::vector<Node> nodes_;
    // When the first run ended, to measure the counter's rate from
    uint64_t rate_start_ = 0;
    std::chrono::steady_clock::time_point rate_start_time_;

    uint64_t start_ops(uint64_t entry, size_t first_id, size_t n_ops);
    uint64_t end_op(size_t i, Op op, TensorType const &type, uint64_t start);
    void end_run(uint64_t entry, uint64_t last_end);

public:
    // The average time of each part of a run, in ns, a line each, at the
    // counter's rate over the time since the first run ended
    std::string report() const;
};

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

    // Benchmarking: where run() adds the time of each part of it, if set
    NodeTimes *node_times_ = nullptr;

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

    // Benchmarking: has run() add the time of each part of it to `times`.
    // Without it, run() only checks, once per node, that it isn't set
    void time_nodes(NodeTimes *const times) noexcept
    {
        node_times_ = times;
    }

    Result<std::vector<Tensor>> run();
};

MONAD_GRAPH_EVAL_NAMESPACE_END
