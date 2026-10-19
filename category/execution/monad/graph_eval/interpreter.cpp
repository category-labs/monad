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

#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/constants.hpp"
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/ops.hpp"
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/interpreter.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <x86intrin.h>

#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <format>
#include <iostream>
#include <iterator>
#include <memory>
#include <span>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// Benchmarking: set to time each node of each evaluation, for
// print_node_times to report
constexpr bool TIME_NODES = false;

// A node of an evaluation: what it computed, and when it finished, as a
// reading of the timestamp counter
struct NodeTime
{
    uint64_t end;
    Op op;
    TensorType type;
};

// The nodes of the thread's last evaluation, until print_node_times reports
// them. The loop over the nodes only reads the timestamp counter and stores
// to this buffer, which has room for the most ops a graph can have. It's
// allocated the first time the thread uses it, uninitialized, so only the
// pages used are ever touched
struct NodeTimes
{
    std::unique_ptr<NodeTime[]> nodes{new NodeTime[size_t{1} << 16]};
    size_t count = 0;
    size_t first_id = 0; // The node id of the first op, after the inputs'
    uint64_t start = 0; // The timestamp counter before the first op
    std::chrono::steady_clock::time_point start_time;
};

NodeTimes &node_times()
{
    thread_local NodeTimes times;
    return times;
}

char const *dtype_name(Dtype const dtype)
{
    switch (dtype) {
    case Dtype::int8:
        return "int8";
    case Dtype::uint8:
        return "uint8";
    case Dtype::int16:
        return "int16";
    case Dtype::uint16:
        return "uint16";
    case Dtype::int32:
        return "int32";
    case Dtype::uint32:
        return "uint32";
    case Dtype::int64:
        return "int64";
    case Dtype::uint64:
        return "uint64";
    }
    MONAD_ABORT();
}

// TensorRef: a tensor copied out of an account's code. Its parameters are a
// tensor header, as for a Literal, the account's address, then the tensor's
// offset in the account's code (uint32), counted from the code's first byte,
// as EXTCODECOPY counts. load_code_tensor reads it, with little-endian
// elements, which must have the type the TensorRef's give.
//
// TODO: give TensorRef a byte order parameter, for consistency with code
// inputs, which have one. TODO: perhaps make TensorRef a GraphOp. It's handled
// ad hoc, here and in the planner, because it would be the only op that reads
// the state, which GraphOp::evaluate has no access to. TODO: charge gas for
// reading the account and copying its code, as EXTCODECOPY does
Result<void>
evaluate_tensor_ref(State &state, TensorRefOp const &op, Tensor &output)
{
    auto const [type, address, offset] = op.params;
    // The planner gave the output the type in the parameters
    CodeRef const ref{address, offset};
    return load_code_tensor(state, ref, ByteOrder::LittleEndian, output);
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<void> Interpreter::check_magic_number()
{
    BOOST_OUTCOME_TRY(auto const magic, read_next<uint16_t>(code_span_));
    if (magic != GRAPH_MAGIC) {
        return GraphEvalError::GraphValidationError;
    }
    return outcome::success();
}

Result<void> Interpreter::check_inputs()
{
    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code_span_));
    if (n_inputs > MAX_GRAPH_INPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    if (n_inputs != inputs_.size()) {
        return GraphEvalError::ArityError;
    }

    for (auto i = 0; i < n_inputs; i++) {
        auto const &input = inputs_[static_cast<size_t>(i)];

        BOOST_OUTCOME_TRY(auto const dtype, read_next<uint8_t>(code_span_));
        if (dtype != static_cast<uint8_t>(input.type.dtype())) {
            return GraphEvalError::TypeError;
        }

        BOOST_OUTCOME_TRY(auto const rank, read_next<uint8_t>(code_span_));
        if (rank != input.type.shape().rank()) {
            return GraphEvalError::RankError;
        }

        for (auto j = 0; j < rank; j++) {
            BOOST_OUTCOME_TRY(auto const d_j, read_next<uint16_t>(code_span_));
            if (d_j != input.type.shape().dimensions()[static_cast<size_t>(j)]) {
                return GraphEvalError::ShapeError;
            }
        }
    }

    return outcome::success();
}

// Copies the inputs into tensors from the allocator, in host byte order, once
// check_inputs has checked their types against the graphcode: a literal's
// elements from the calldata, and a reference's from an account's code or the
// caller's storage. InvalidTensorRef for the first reference whose data
// doesn't match its type
Result<void> Interpreter::load_inputs()
{
    for (size_t i = 0; i < inputs_.size(); i++) {
        TensorInput const &input = inputs_[i];
        Tensor &tensor = node_values_[i];
        if (auto const *const data =
                std::get_if<byte_string_view>(&input.source)) {
            copy_elements(
                input.type.dtype(), input.byte_order, *data, tensor.data());
        }
        else if (auto const *const ref = std::get_if<CodeRef>(&input.source)) {
            BOOST_OUTCOME_TRY(
                load_code_tensor(state_, *ref, input.byte_order, tensor));
        }
        else {
            // Storage references outside a DELEGATECALL were rejected before
            MONAD_ASSERT(caller_storage_ != nullptr);
            BOOST_OUTCOME_TRY(load_storage_tensor(
                *caller_storage_,
                std::get<StorageRef>(input.source),
                input.byte_order,
                tensor));
        }
    }
    return outcome::success();
}

Result<void> Interpreter::prepare_node_placement()
{
    if (graphcode_.validation_result() != GraphEvalError::Success) {
        return graphcode_.validation_result();
    }
    auto const &allocs = graphcode_.tensor_allocation_records();
    node_values_.reserve(allocs.size());
    for (auto const alloc : allocs) {
        Tensor tensor{alloc.type, arena_ + alloc.offset};
        node_values_.push_back(tensor);
    }
    return outcome::success();
}

Result<std::vector<Tensor>> Interpreter::run()
{
    BOOST_OUTCOME_TRY(check_magic_number());
    BOOST_OUTCOME_TRY(check_inputs());
    BOOST_OUTCOME_TRY(prepare_node_placement());

    auto const n_inputs = inputs_.size();
    // Read output-tensor indices. TODO: constrain number of outputs
    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(code_span_));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    if (output_count_.has_value() && *output_count_ != n_outputs) {
        return GraphEvalError::ArityError;
    }
    std::array<uint16_t, MAX_GRAPH_OUTPUTS> outputs{};
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(outputs[i], read_next<uint16_t>(code_span_));
    }

    // After everything static, so that reference errors come after those
    BOOST_OUTCOME_TRY(load_inputs());

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code_span_));
    NodeTimes *const times = TIME_NODES ? &node_times() : nullptr;
    if constexpr (TIME_NODES) {
        times->count = 0;
        times->first_id = n_inputs;
        times->start_time = std::chrono::steady_clock::now();
        times->start = __rdtsc();
    }
    for (size_t i = 0; i < n_ops; i++) {
        // OutputAllocator const output{allocator_, node_values_.size()};
        Tensor &result = node_values_[n_inputs + i];
        Op opcode{};
        BOOST_OUTCOME_TRY(
            visit_next(code_span_, [&]<typename OpT>(OpT const &op) {
                opcode = OpT::OPCODE;
                if constexpr (std::same_as<OpT, TensorRefOp>) {
                    // TODO: fold this into normal evaluation
                    return evaluate_tensor_ref(state_, op, result);
                }
                else {
                    return op.evaluate(result, node_values_);
                }
            }));

        if constexpr (TIME_NODES) {
            times->nodes[times->count++] =
                NodeTime{__rdtsc(), opcode, result.type()};
        }
    }

    // Output indices are read before the ops, so they can only be checked once
    // every node exists
    std::vector<Tensor> output_values;
    output_values.reserve(n_outputs);
    for (size_t i = 0; i < n_outputs; i++) {
        if (outputs[i] >= node_values_.size()) {
            return GraphEvalError::GraphValidationError;
        }
        output_values.push_back(node_values_[outputs[i]]);
    }
    return output_values;
}

void print_node_times()
{
    NodeTimes &times = node_times();
    if (times.count == 0) {
        return;
    }

    // The timestamp counter's rate, over the time since the first op started
    uint64_t const now = __rdtsc();
    auto const now_time = std::chrono::steady_clock::now();
    double const ns_per_tick =
        std::chrono::duration<double, std::nano>(now_time - times.start_time)
            .count() /
        static_cast<double>(now - times.start);
    auto const microseconds = [&](uint64_t const ticks) {
        return static_cast<double>(ticks) * ns_per_tick / 1000;
    };

    std::string report;
    auto out = std::back_inserter(report);
    std::format_to(
        out,
        "evalGraph: {} nodes in {:.3f} µs\n",
        times.count,
        microseconds(times.nodes[times.count - 1].end - times.start));
    uint64_t previous = times.start;
    std::string type;
    for (size_t i = 0; i < times.count; i++) {
        NodeTime const &node = times.nodes[i];
        Shape const &shape = node.type.shape();
        type = dtype_name(node.type.dtype());
        type += '[';
        for (size_t d = 0; d < shape.rank(); d++) {
            std::format_to(
                std::back_inserter(type),
                "{}{}",
                d == 0 ? "" : ", ",
                shape.dimensions()[d]);
        }
        type += ']';
        std::format_to(
            out,
            "  node {:>5} {:<10} {:<24} {:>10.3f} µs\n",
            times.first_id + i,
            op_name(node.op),
            type,
            microseconds(node.end - previous));
        previous = node.end;
    }
    times.count = 0;
    std::cout << report;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
