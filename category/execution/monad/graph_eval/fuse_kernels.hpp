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

// What fuse_claude and FusedInterpreter share: the reading and checking of
// an op's core and instructions, and the kernels of the cores and
// instructions, given their chunks' elements directly

#include <category/execution/monad/graph_eval/broadcasting.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/fuse_claude.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/matmul.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <category/core/assert.h>
#include <category/core/result.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <concepts>
#include <cstdint>
#include <cstring>
#include <functional>
#include <optional>
#include <span>
#include <tuple>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

namespace fuse_kernels
{
    // An op's core, with its parameters
    struct Core
    {
        FusedCore core;
        std::array<size_t, 2> inputs{};
        // Its result's type, which its op checks, but for a Map's
        std::optional<TensorType> type;
        uint8_t axis = 0;
        // A Literal's elements, a TensorRef's tensor, a QMatMul's bits
        std::span<uint8_t const> literal;
        CodeRef ref{};
        uint8_t bits = 0;
    };

    // Reads an op's core and checks it as its op checks its inputs, given
    // the types of the nodes so far
    inline Result<Core> read_core(
        std::span<uint8_t const> &code, std::vector<TensorType> const &types)
    {
        BOOST_OUTCOME_TRY(auto const id, read_next<uint8_t>(code));
        if (id > static_cast<uint8_t>(FusedCore::Last_valid)) {
            return GraphEvalError::GraphValidationError;
        }
        Core core{static_cast<FusedCore>(id)};
        auto const read_id = [&]() -> Result<size_t> {
            BOOST_OUTCOME_TRY(auto const node, read_next<uint16_t>(code));
            if (node >= types.size()) {
                return GraphEvalError::GraphValidationError;
            }
            return node;
        };
        auto const read_inputs = [&](size_t const n) -> Result<void> {
            for (size_t i = 0; i < n; i++) {
                BOOST_OUTCOME_TRY(core.inputs[i], read_id());
            }
            return outcome::success();
        };
        auto const check = [&]<typename Op>(Op const &op) -> Result<void> {
            if constexpr (Op::ARITY == 1) {
                BOOST_OUTCOME_TRY(
                    core.type, op.check_impl({&types[core.inputs[0]]}));
            }
            else {
                BOOST_OUTCOME_TRY(
                    core.type,
                    op.check_impl(
                        {&types[core.inputs[0]], &types[core.inputs[1]]}));
            }
            return outcome::success();
        };
        // An op whose parameter is the axis
        auto const along_axis =
            [&]<typename Op>(size_t const n_inputs) -> Result<void> {
            BOOST_OUTCOME_TRY(core.axis, read_next<uint8_t>(code));
            BOOST_OUTCOME_TRY(read_inputs(n_inputs));
            Op op{};
            op.params = core.axis;
            return check(op);
        };
        switch (core.core) {
        case FusedCore::Map:
            break;
        case FusedCore::Literal: {
            using Params = std::tuple<TensorType, std::span<uint8_t const>>;
            BOOST_OUTCOME_TRY(auto const params, read_next<Params>(code));
            core.type = std::get<0>(params);
            core.literal = std::get<1>(params);
            break;
        }
        case FusedCore::TensorRef: {
            using Params = std::tuple<TensorType, Address, uint32_t>;
            BOOST_OUTCOME_TRY(auto const params, read_next<Params>(code));
            core.type = std::get<0>(params);
            core.ref = CodeRef{std::get<1>(params), std::get<2>(params)};
            break;
        }
        case FusedCore::QMatMul:
        case FusedCore::QMatMulEager: {
            QMatMulOp op{};
            BOOST_OUTCOME_TRY(
                op.params, read_next<std::tuple<uint8_t, Dtype>>(code));
            core.bits = std::get<0>(op.params);
            BOOST_OUTCOME_TRY(read_inputs(2));
            BOOST_OUTCOME_TRY(check(op));
            break;
        }
        case FusedCore::ReduceSum:
        case FusedCore::ReduceSumEager: {
            BOOST_OUTCOME_TRY(along_axis.template operator()<ReduceSumOp>(1));
            break;
        }
        case FusedCore::ReduceMax:
        case FusedCore::ReduceMaxEager: {
            BOOST_OUTCOME_TRY(along_axis.template operator()<ReduceMaxOp>(1));
            break;
        }
        case FusedCore::CumSum:
        case FusedCore::CumSumEager: {
            BOOST_OUTCOME_TRY(along_axis.template operator()<CumSumOp>(1));
            break;
        }
        case FusedCore::Gather: {
            BOOST_OUTCOME_TRY(core.axis, read_next<uint8_t>(code));
            BOOST_OUTCOME_TRY(read_inputs(2));
            GatherOp op{};
            op.params = core.axis;
            BOOST_OUTCOME_TRY(check(op));
            break;
        }
        case FusedCore::Concat: {
            BOOST_OUTCOME_TRY(core.axis, read_next<uint8_t>(code));
            BOOST_OUTCOME_TRY(read_inputs(2));
            BOOST_OUTCOME_TRY(
                core.type,
                ConcatOp::type(
                    core.axis, types[core.inputs[0]], types[core.inputs[1]]));
            break;
        }
        case FusedCore::MatMul:
        case FusedCore::MatMulEager: {
            BOOST_OUTCOME_TRY(read_inputs(2));
            BOOST_OUTCOME_TRY(check(MatMulOp{}));
            break;
        }
        case FusedCore::ArgMax:
        case FusedCore::ArgMaxEager: {
            BOOST_OUTCOME_TRY(read_inputs(1));
            BOOST_OUTCOME_TRY(check(ArgMaxOp{}));
            break;
        }
        case FusedCore::Reshape: {
            ReshapeOp op{};
            BOOST_OUTCOME_TRY(op.params, read_next<Shape>(code));
            BOOST_OUTCOME_TRY(read_inputs(1));
            BOOST_OUTCOME_TRY(check(op));
            break;
        }
        }
        return core;
    }

    // An instruction, with its parameters
    struct Instruction
    {
        FusedInstruction opcode;
        // An Input's node, or a Gather's data
        size_t input_id = 0;
        // The Constant's dtype, or the one Saturate converts to
        Dtype dtype = Dtype::int8;
        // The Constant's element, at the start
        uint64_t constant = 0;
        // Div's denominator, or a fixed-point instruction's bits
        int64_t parameter = 0;
        // A Gather's indices and axis
        size_t index_id = 0;
        uint8_t axis = 0;
    };

    // Reads an op's instructions, of which Core is one only if the op has a
    // core, given the number of nodes so far
    inline Result<std::vector<Instruction>> read_instructions(
        std::span<uint8_t const> &code, size_t const n_nodes,
        bool const has_core)
    {
        BOOST_OUTCOME_TRY(auto const n_instructions, read_next<uint8_t>(code));
        if (n_instructions > MAX_FUSED_INSTRUCTIONS) {
            return GraphEvalError::GraphValidationError;
        }
        auto const read_id = [&]() -> Result<size_t> {
            BOOST_OUTCOME_TRY(auto const node, read_next<uint16_t>(code));
            if (node >= n_nodes) {
                return GraphEvalError::GraphValidationError;
            }
            return node;
        };
        std::vector<Instruction> instructions;
        for (size_t i = 0; i < n_instructions; i++) {
            BOOST_OUTCOME_TRY(auto const opcode, read_next<uint8_t>(code));
            if (opcode > static_cast<uint8_t>(FusedInstruction::Last_valid)) {
                return GraphEvalError::GraphValidationError;
            }
            Instruction instruction{static_cast<FusedInstruction>(opcode)};
            switch (instruction.opcode) {
            case FusedInstruction::Core: {
                if (!has_core) {
                    return GraphEvalError::GraphValidationError;
                }
                break;
            }
            case FusedInstruction::Input: {
                BOOST_OUTCOME_TRY(instruction.input_id, read_id());
                break;
            }
            case FusedInstruction::Constant: {
                BOOST_OUTCOME_TRY(instruction.dtype, read_next<Dtype>(code));
                BOOST_OUTCOME_TRY(
                    instruction.constant,
                    visit_dtype(
                        instruction.dtype,
                        [&]<typename T>() -> Result<uint64_t> {
                            BOOST_OUTCOME_TRY(auto const x, read_next<T>(code));
                            uint64_t constant = 0;
                            std::memcpy(&constant, &x, sizeof(x));
                            return constant;
                        }));
                break;
            }
            case FusedInstruction::Div: {
                BOOST_OUTCOME_TRY(
                    instruction.parameter, read_next<int64_t>(code));
                if (instruction.parameter == 0) {
                    return GraphEvalError::GraphValidationError;
                }
                break;
            }
            case FusedInstruction::Saturate: {
                BOOST_OUTCOME_TRY(instruction.dtype, read_next<Dtype>(code));
                break;
            }
            case FusedInstruction::Gather: {
                BOOST_OUTCOME_TRY(instruction.input_id, read_id());
                BOOST_OUTCOME_TRY(instruction.index_id, read_id());
                BOOST_OUTCOME_TRY(instruction.axis, read_next<uint8_t>(code));
                break;
            }
            default: {
                if (has_fractional_bits(instruction.opcode)) {
                    BOOST_OUTCOME_TRY(
                        auto const bits, read_next<uint8_t>(code));
                    if (bits > MAX_FRACTIONAL_BITS) {
                        return GraphEvalError::GraphValidationError;
                    }
                    instruction.parameter = bits;
                }
                break;
            }
            }
            instructions.push_back(instruction);
        }
        return instructions;
    }

    // Copies the elements of xs that the chunk of `length` elements from
    // `start` of the result reads, broadcast through `loops`: finds where the
    // chunk starts in the loops, then copies runs along the innermost loop,
    // advancing the outer ones like an odometer
    template <typename T>
    void broadcast_chunk(
        BroadcastLoops<2> const &loops, T const *const xs, T *const outs,
        uint64_t const start, uint64_t const length)
    {
        auto const &strides = loops.strides[1];
        std::array<uint64_t, MAX_RANK> index;
        uint64_t offset = 0;
        uint64_t position = start;
        for (size_t d = 0; d < loops.rank; d++) {
            index[d] = position % loops.lengths[d];
            position /= loops.lengths[d];
            offset += index[d] * strides[d];
        }
        for (uint64_t done = 0; done < length;) {
            uint64_t const run =
                std::min(loops.lengths[0] - index[0], length - done);
            run_op1<std::identity>(
                xs + offset, outs + done, run, strides[0] != 0);
            done += run;
            index[0] += run;
            offset += run * strides[0];
            for (size_t d = 0;
                 d + 1 < loops.rank && index[d] == loops.lengths[d];
                 d++) {
                index[d] = 0;
                offset -= loops.lengths[d] * strides[d];
                index[d + 1]++;
                offset += strides[d + 1];
            }
        }
    }

    // A Gather instruction's result's type, given the nodes' types. It must
    // be one contiguous slice of the data: one index, along an axis before
    // which every dimension is 1
    inline Result<TensorType>
    gather_type(std::vector<TensorType> const &types, Instruction const &gather)
    {
        TensorType const &data = types[gather.input_id];
        TensorType const &indices = types[gather.index_id];
        uint8_t const axis = gather.axis;
        GatherOp op{};
        op.params = axis;
        BOOST_OUTCOME_TRY(auto const type, op.check_impl({&data, &indices}));
        if (indices.shape().size() != 1 ||
            dimensions_product(data.shape(), 0, axis) != 1) {
            return GraphEvalError::GraphValidationError;
        }
        return type;
    }

    // A Gather's index: the index tensor's one element, of `dtype`, if it's
    // in [0, length)
    inline std::optional<uint64_t> gather_index(
        uint8_t const *const index, Dtype const dtype, uint64_t const length)
    {
        return visit_dtype(dtype, [&]<typename I>() -> std::optional<uint64_t> {
            I value;
            std::memcpy(&value, index, sizeof(I));
            if (std::cmp_less(value, 0) ||
                std::cmp_greater_equal(value, length)) {
                return std::nullopt;
            }
            return static_cast<uint64_t>(value);
        });
    }

    // QDiv's check: DivisionByZero for a zero denominator among `n`
    inline GraphEvalError
    check_denominators(auto const *const ys, uint64_t const n)
    {
        for (uint64_t i = 0; i < n; i++) {
            if (ys[i] == 0) {
                return GraphEvalError::DivisionByZero;
            }
        }
        return GraphEvalError::Success;
    }

    // QInvSqrt's check: of `n` elements, the first that isn't positive fails,
    // with DivisionByZero if it's zero and DomainError if it's negative
    inline GraphEvalError check_inv_sqrt(auto const *const xs, uint64_t const n)
    {
        for (uint64_t i = 0; i < n; i++) {
            if (xs[i] == 0) {
                return GraphEvalError::DivisionByZero;
            }
            if (std::cmp_less(xs[i], 0)) {
                return GraphEvalError::DomainError;
            }
        }
        return GraphEvalError::Success;
    }

    // A reduction's results from `start` to `start + length - 1`, for an input
    // of blocks of `rows` rows of `inner` elements, with the axis running down
    // the rows: result e combines column e % inner of block e / inner with F.
    // An empty axis gives zeros, as ReduceSum's does. With one element a row,
    // result e is block e, a contiguous run
    template <typename T, typename F>
    void reduce_chunk(
        T const *const xs, T *const outs, uint64_t const start,
        uint64_t const length, uint64_t const rows, uint64_t const inner)
    {
        if (inner == 1 && rows > 0) {
            for (uint64_t done = 0; done < length; done++) {
                outs[done] =
                    reduce_contiguous<T, F>(xs + (start + done) * rows, rows);
            }
            return;
        }
        for (uint64_t done = 0; done < length;) {
            uint64_t const e = start + done;
            uint64_t const column = e % inner;
            uint64_t const run = std::min(inner - column, length - done);
            T const *const first = xs + e / inner * rows * inner + column;
            T *const out = outs + done;
            if (rows == 0) {
                std::fill_n(out, run, T{0});
            }
            else {
                std::copy_n(first, run, out);
                for (uint64_t row = 1; row < rows; row++) {
                    reduce_row<T, F>(out, first + row * inner, run);
                }
            }
            done += run;
        }
    }

    // The whole result of CumSumEager, ArgMaxEager, ReduceSumEager or
    // ReduceMaxEager, as Op, the reference interpreter's op, evaluates it, with
    // `axis` its parameter but for ArgMax. Success, or the op's error
    template <typename Op>
    GraphEvalError
    evaluate_whole(uint8_t const axis, Tensor const &x, Tensor &out)
    {
        Op op{};
        if constexpr (std::same_as<typename Op::Parameters, uint8_t>) {
            op.params = axis;
        }
        auto const result = op.evaluate_impl(out, {&x});
        return result.has_error()
                   ? static_cast<GraphEvalError>(result.error().value())
                   : GraphEvalError::Success;
    }

    // A Gather core's whole result, as the Gather op evaluates it: IndexError
    // for an index out of range
    inline GraphEvalError evaluate_gather(
        uint8_t const axis, Tensor const &data, Tensor const &indices,
        Tensor &out)
    {
        GatherOp op{};
        op.params = axis;
        auto const result = op.evaluate_impl(out, {&data, &indices});
        return result.has_error()
                   ? static_cast<GraphEvalError>(result.error().value())
                   : GraphEvalError::Success;
    }

    // evaluate_whole for the core, which is one of those four
    inline GraphEvalError evaluate_eager(
        FusedCore const core, uint8_t const axis, Tensor const &x, Tensor &out)
    {
        switch (core) {
        case FusedCore::CumSumEager:
            return evaluate_whole<CumSumOp>(axis, x, out);
        case FusedCore::ArgMaxEager:
            return evaluate_whole<ArgMaxOp>(axis, x, out);
        case FusedCore::ReduceSumEager:
            return evaluate_whole<ReduceSumOp>(axis, x, out);
        case FusedCore::ReduceMaxEager:
            return evaluate_whole<ReduceMaxOp>(axis, x, out);
        default:
            MONAD_ABORT();
        }
    }

    // A Concat's whole result: `blocks` blocks, each a's `a_bytes` then b's
    // `b_bytes`, as the Concat op copies them
    inline void concat(
        uint8_t const *const a, uint8_t const *const b, uint8_t *out,
        uint64_t const blocks, uint64_t const a_bytes, uint64_t const b_bytes)
    {
        for (uint64_t block = 0; block < blocks; block++) {
            std::memcpy(out, a + block * a_bytes, a_bytes);
            out += a_bytes;
            std::memcpy(out, b + block * b_bytes, b_bytes);
            out += b_bytes;
        }
    }

    // A rows x columns matrix of `dtype` at `data`, which fits, since its
    // dimensions are at most those of tensors already checked
    inline Tensor matrix(
        Dtype const dtype, uint64_t const rows, uint64_t const columns,
        void *const data)
    {
        auto const shape = Shape::checked(
            2, {static_cast<uint16_t>(rows), static_cast<uint16_t>(columns)});
        return Tensor{
            TensorType::checked(dtype, shape.value()).value(),
            static_cast<uint8_t *>(data)};
    }

    // QMatMul's product of `rows` rows of x, `inner` long, with y, which is
    // `inner` x `columns`, as the QMatMul op computes it
    inline void qmatmul(
        Dtype const dtype, Dtype const out_dtype, unsigned const bits,
        void *const x, void *const y, void *const out, uint64_t const rows,
        uint64_t const inner, uint64_t const columns)
    {
        Tensor product = matrix(out_dtype, rows, columns, out);
        matmul(
            matrix(dtype, rows, inner, x),
            matrix(dtype, inner, columns, y),
            bits,
            product);
    }
}

MONAD_GRAPH_EVAL_NAMESPACE_END
