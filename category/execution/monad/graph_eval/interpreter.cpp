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
#include <category/execution/monad/graph_eval/interpreter.hpp>
#include <category/execution/monad/graph_eval/kernel.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <array>
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>

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
        if (dtype != static_cast<uint8_t>(input.dtype)) {
            return GraphEvalError::TypeError;
        }

        BOOST_OUTCOME_TRY(auto const rank, read_next<uint8_t>(code_span_));
        if (rank != input.shape.rank) {
            return GraphEvalError::RankError;
        }

        for (auto j = 0; j < rank; j++) {
            BOOST_OUTCOME_TRY(auto const d_j, read_next<uint16_t>(code_span_));
            if (d_j != input.shape.dimensions[static_cast<size_t>(j)]) {
                return GraphEvalError::ShapeError;
            }
        }
    }

    return outcome::success();
}

// Copies the inputs out of the calldata into tensors from the allocator, in
// host byte order, once check_inputs has checked them against the graphcode
Result<void> Interpreter::load_inputs()
{
    size_t i = 0;
    for (EncodedTensor const &input : inputs_) {
        abi_load_tensor_data(input, node_values_[i].data());
        i += 1;
    }
    return outcome::success();
}

Result<void> Interpreter::prepare_node_placement()
{
    // Making this const means it can't be cast to Result<void> for some reason
    auto validation_result = graphcode_.validation_result();
    if (validation_result != GraphEvalError::Success) {
        return validation_result;
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
    BOOST_OUTCOME_TRY(load_inputs());

    auto const n_inputs = inputs_.size();
    // Read output-tensor indices. TODO: constrain number of outputs
    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(code_span_));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    std::array<uint16_t, MAX_GRAPH_OUTPUTS> outputs{};
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(outputs[i], read_next<uint16_t>(code_span_));
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code_span_));
    for (size_t i = 0; i < n_ops; i++) {
        BOOST_OUTCOME_TRY(
            auto const opcode_id, read_next<uint16_t>(code_span_));
        if (opcode_id > static_cast<uint16_t>(Op::Last_valid_op)) {
            return GraphEvalError::GraphValidationError;
        }
        auto const opcode = static_cast<Op>(opcode_id);
        // OutputAllocator const output{allocator_, node_values_.size()};

        Tensor &result = node_values_[n_inputs + i];
        switch (opcode) {
        case Op::Literal: {
            BOOST_OUTCOME_TRY(LiteralOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::TensorRef: {
            return GraphEvalError::InternalError;
            break;
        }
        case Op::Add: {
            BOOST_OUTCOME_TRY(AddOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Sub: {
            BOOST_OUTCOME_TRY(SubOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Greater: {
            BOOST_OUTCOME_TRY(GreaterOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Ge: {
            BOOST_OUTCOME_TRY(GeOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Equal: {
            BOOST_OUTCOME_TRY(EqualOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Reshape: {
            BOOST_OUTCOME_TRY(ReshapeOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Where: {
            BOOST_OUTCOME_TRY(WhereOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::CumSum: {
            BOOST_OUTCOME_TRY(CumSumOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Saturate: {
            BOOST_OUTCOME_TRY(SaturateOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::MatMul: {
            BOOST_OUTCOME_TRY(MatMulOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::ArgMax: {
            BOOST_OUTCOME_TRY(ArgMaxOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::ArgMin: {
            return GraphEvalError::InternalError;
            break;
        }
        case Op::Clip: {
            return GraphEvalError::InternalError;
            break;
        }
        case Op::Max: {
            BOOST_OUTCOME_TRY(MaxOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Min: {
            BOOST_OUTCOME_TRY(MinOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Mul: {
            BOOST_OUTCOME_TRY(MulOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Div: {
            BOOST_OUTCOME_TRY(DivOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
        case Op::Cast: {
            return GraphEvalError::InternalError;
            break;
        }
        case Op::Expand: {
            BOOST_OUTCOME_TRY(ExpandOp{}.evaluate(code_span_, result, node_values_));
            break;
        }
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

MONAD_GRAPH_EVAL_NAMESPACE_END
