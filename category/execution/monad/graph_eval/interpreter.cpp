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
#include <iterator>
#include <span>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

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
    uint64_t const entry = node_times_ ? __rdtsc() : 0;
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
    uint64_t op_start =
        node_times_ ? node_times_->start_ops(entry, n_inputs, n_ops) : 0;
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

        if (node_times_) {
            op_start = node_times_->end_op(i, opcode, result.type(), op_start);
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
    if (node_times_) {
        node_times_->end_run(entry, op_start);
    }
    return output_values;
}

// The counter after the setup, before the first op
uint64_t NodeTimes::start_ops(
    uint64_t const entry, size_t const first_id, size_t const n_ops)
{
    uint64_t const now = __rdtsc();
    setup_ += now - entry;
    first_id_ = first_id;
    if (nodes_.size() != n_ops) {
        nodes_.resize(n_ops);
    }
    return now;
}

// The counter after op i, which started at `start`. Its op and type are
// recorded from the first run only, so that later runs only add its time
uint64_t NodeTimes::end_op(
    size_t const i, Op const op, TensorType const &type, uint64_t const start)
{
    uint64_t const now = __rdtsc();
    Node &node = nodes_[i];
    node.ticks += now - start;
    if (runs_ == 0) {
        node.op = op;
        node.type = type;
    }
    return now;
}

void NodeTimes::end_run(uint64_t const entry, uint64_t const last_end)
{
    uint64_t const now = __rdtsc();
    outputs_ += now - last_end;
    total_ += now - entry;
    if (runs_++ == 0) {
        rate_start_time_ = std::chrono::steady_clock::now();
        rate_start_ = __rdtsc();
    }
}

std::string NodeTimes::report() const
{
    if (runs_ < 2) {
        return "too few runs timed by node\n";
    }
    uint64_t const now = __rdtsc();
    auto const now_time = std::chrono::steady_clock::now();
    double const ns_per_tick =
        std::chrono::duration<double, std::nano>(now_time - rate_start_time_)
            .count() /
        static_cast<double>(now - rate_start_);
    auto const average = [&](uint64_t const ticks) {
        return static_cast<double>(ticks) * ns_per_tick /
               static_cast<double>(runs_);
    };
    // What a read of the counter, which each part includes one of, takes
    constexpr uint64_t READS = 100000;
    uint64_t read_ticks = 0;
    for (uint64_t i = 0; i < READS; i++) {
        uint64_t const before = __rdtsc();
        read_ticks += __rdtsc() - before;
    }

    std::string report;
    auto out = std::back_inserter(report);
    std::format_to(
        out,
        "{:.1f} ns a run, over {} runs; each part includes a read of the "
        "timestamp counter, which takes {:.1f} ns\n",
        average(total_),
        runs_,
        static_cast<double>(read_ticks) * ns_per_tick /
            static_cast<double>(READS));
    std::format_to(
        out,
        "  {:<46} {:>9.1f} ns\n",
        "setup, before the first op",
        average(setup_));
    std::string type;
    for (size_t i = 0; i < nodes_.size(); i++) {
        Node const &node = nodes_[i];
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
            "  node {:>5} {:<10} {:<24} {:>9.1f} ns\n",
            first_id_ + i,
            op_name(node.op),
            type,
            average(node.ticks));
    }
    std::format_to(
        out,
        "  {:<46} {:>9.1f} ns\n",
        "outputs, after the last op",
        average(outputs_));
    return report;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
