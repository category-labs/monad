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

#include "category/core/assert.h"
#include "category/core/math.hpp"
#include "category/execution/monad/graph_eval/broadcasting.hpp"
#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/constants.hpp"
#include "category/execution/monad/graph_eval/fuse_kernels.hpp"
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/matmul.hpp"
#include "category/execution/monad/graph_eval/ops.hpp"
#include "category/execution/monad/graph_eval/references.hpp"
#include <category/execution/monad/graph_eval/fuse_claude.hpp>

#include <algorithm>
#include <bit>
#include <concepts>
#include <cstdint>
#include <cstring>
#include <functional>
#include <initializer_list>
#include <optional>
#include <type_traits>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

using StepFn = decltype(FusedStep::run);

template <typename F, typename T>
using out_t = std::conditional_t<
    std::same_as<std::invoke_result_t<F, T, T>, bool>, uint8_t,
    std::invoke_result_t<F, T, T>>;

template <typename T>
T *chunk_at(
    FusedOperand const &operand, uint64_t const start,
    kernel_memory_arenas &arenas)
{
    return reinterpret_cast<T *>(
        arenas[static_cast<size_t>(operand.place.arena)] +
        operand.place.offset + start * operand.advance);
}

template <typename T>
GraphEvalError copy_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    run_op1<std::identity>(
        chunk_at<T const>(step.inputs[0], start, arenas),
        chunk_at<T>(step.output, start, arenas),
        length,
        step.inputs[0].stride);
    return GraphEvalError::Success;
}

// Finds where the chunk starts in the loops, then copies the Input's runs
// along the innermost loop, advancing the outer ones like an odometer
template <typename T>
GraphEvalError broadcast_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    fuse_kernels::broadcast_chunk(
        step.loops,
        chunk_at<T const>(step.inputs[0], 0, context.arenas),
        chunk_at<T>(step.output, start, context.arenas),
        start,
        length);
    return GraphEvalError::Success;
}

template <typename T, typename F>
GraphEvalError binary_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    run_op2<F>(
        chunk_at<T const>(step.inputs[0], start, arenas),
        chunk_at<T const>(step.inputs[1], start, arenas),
        chunk_at<out_t<F, T>>(step.output, start, arenas),
        length,
        step.inputs[0].stride,
        step.inputs[1].stride);
    return GraphEvalError::Success;
}

template <typename T>
GraphEvalError where_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    run_op3<WhereOp::Impl<T>>(
        chunk_at<uint8_t const>(step.inputs[0], start, arenas),
        chunk_at<T const>(step.inputs[1], start, arenas),
        chunk_at<T const>(step.inputs[2], start, arenas),
        chunk_at<T>(step.output, start, arenas),
        length,
        step.inputs[0].stride,
        step.inputs[1].stride,
        step.inputs[2].stride);
    return GraphEvalError::Success;
}

// Adds part of a row to the running sums, which are also the results. The
// restrict pointers let GCC vectorize the loops without checking for overlap,
// which it doesn't do at -O2
template <typename T>
[[gnu::always_inline]]
inline void add_row(
    T const *__restrict const xs, T *__restrict const sums,
    T *__restrict const outs, uint64_t const length, bool const first_row)
{
    if (first_row) {
        for (uint64_t i = 0; i < length; i++) {
            sums[i] = xs[i];
            outs[i] = xs[i];
        }
    }
    else {
        for (uint64_t i = 0; i < length; i++) {
            T const sum = WrappingAdd{}(sums[i], xs[i]);
            sums[i] = sum;
            outs[i] = sum;
        }
    }
}

// The chunks come in order, so each element's running sum is the one above it
// in the previous row, which is kept in the row of sums from chunk to chunk
template <typename T>
GraphEvalError cumsum_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    T const *const xs = chunk_at<T const>(step.inputs[0], start, arenas);
    T *const sums = chunk_at<T>(step.inputs[1], start, arenas);
    T *const outs = chunk_at<T>(step.output, start, arenas);
    uint64_t column = start % step.inner;
    uint64_t row = start / step.inner % step.rows;
    for (uint64_t i = 0; i < length;) {
        uint64_t const run = std::min(step.inner - column, length - i);
        add_row(xs + i, sums + column, outs + i, run, row == 0);
        i += run;
        column += run;
        if (column == step.inner) {
            column = 0;
            row = row + 1 == step.rows ? 0 : row + 1;
        }
    }
    return GraphEvalError::Success;
}

// The chunk's rows of the product, from the same rows of x and all of y. A
// matrix times a vector is a dot product a row, as in the lite compiler
GraphEvalError matmul_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    uint64_t const first_row = start / step.columns;
    uint64_t const rows = length / step.columns;
    auto *const xs =
        chunk_at<int8_t>(step.inputs[0], 0, arenas) + first_row * step.inner;
    auto *const ys = chunk_at<int8_t>(step.inputs[1], 0, arenas);
    auto *const outs = chunk_at<int32_t>(step.output, start, arenas);
    if (step.columns == 1) {
        for (uint64_t row = 0; row < rows; row++) {
            // Can't overflow: at most 65535 products of magnitude 2^14
            int32_t sum = 0;
            for (uint64_t i = 0; i < step.inner; i++) {
                sum += int32_t{xs[row * step.inner + i]} * int32_t{ys[i]};
            }
            outs[row] = sum;
        }
        return GraphEvalError::Success;
    }
    using fuse_kernels::matrix;
    Tensor out = matrix(Dtype::int32, rows, step.columns, outs);
    matmul_i8(
        matrix(Dtype::int8, rows, step.inner, xs),
        matrix(Dtype::int8, step.inner, step.columns, ys),
        out);
    return GraphEvalError::Success;
}

// The whole product, at the op's first chunk, before the instructions read
// it, as the MatMul op computes it: a matrix times a vector a dot product a
// row, with matvec_i8, else with matmul_i8. `rows`, `inner` and `columns` are
// the product's m, k and n
GraphEvalError matmul_eager_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    if (start != 0) {
        return GraphEvalError::Success;
    }
    auto *const xs = chunk_at<int8_t>(step.inputs[0], 0, arenas);
    auto *const ys = chunk_at<int8_t>(step.inputs[1], 0, arenas);
    auto *const outs = chunk_at<int32_t>(step.output, 0, arenas);
    if (step.columns == 1) {
        matvec_i8(xs, ys, outs, step.rows, step.inner);
        return GraphEvalError::Success;
    }
    using fuse_kernels::matrix;
    Tensor out = matrix(Dtype::int32, step.rows, step.columns, outs);
    matmul_i8(
        matrix(Dtype::int8, step.rows, step.inner, xs),
        matrix(Dtype::int8, step.inner, step.columns, ys),
        out);
    return GraphEvalError::Success;
}

// The whole input's ArgMax, as the result has a single element
template <typename T>
GraphEvalError argmax_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    T const *const xs = chunk_at<T const>(step.inputs[0], 0, arenas);
    uint64_t largest = 0;
    for (uint64_t i = 1; i < step.inner; i++) {
        if (xs[largest] < xs[i]) {
            largest = i;
        }
    }
    *chunk_at<T>(step.output, start, arenas) = static_cast<T>(largest);
    return GraphEvalError::Success;
}

// The whole result of CumSumEager, ArgMaxEager, ReduceSumEager or
// ReduceMaxEager, at the op's first chunk, as Op, the reference interpreter's
// op, evaluates it. `parameter` is the axis
template <typename Op>
GraphEvalError eager_op_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    if (start != 0) {
        return GraphEvalError::Success;
    }
    Tensor const x{
        step.input_type, chunk_at<uint8_t>(step.inputs[0], 0, context.arenas)};
    Tensor out{step.type, chunk_at<uint8_t>(step.output, 0, context.arenas)};
    return fuse_kernels::evaluate_whole<Op>(
        static_cast<uint8_t>(step.parameter), x, out);
}

// A Gather core's whole result, at the op's first chunk, as the Gather op
// evaluates it. `parameter` is the axis
GraphEvalError gather_core_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    if (start != 0) {
        return GraphEvalError::Success;
    }
    Tensor const data{
        step.input_type, chunk_at<uint8_t>(step.inputs[0], 0, context.arenas)};
    Tensor const indices{
        step.index_type, chunk_at<uint8_t>(step.inputs[1], 0, context.arenas)};
    Tensor out{step.type, chunk_at<uint8_t>(step.output, 0, context.arenas)};
    return fuse_kernels::evaluate_gather(
        static_cast<uint8_t>(step.parameter), data, indices, out);
}

// The step of CumSumEager, ArgMaxEager, ReduceSumEager or ReduceMaxEager, or
// null for any other core
StepFn eager_op_step_for(FusedCore const core)
{
    switch (core) {
    case FusedCore::CumSumEager:
        return &eager_op_step<CumSumOp>;
    case FusedCore::ArgMaxEager:
        return &eager_op_step<ArgMaxOp>;
    case FusedCore::ReduceSumEager:
        return &eager_op_step<ReduceSumOp>;
    case FusedCore::ReduceMaxEager:
        return &eager_op_step<ReduceMaxOp>;
    default:
        return nullptr;
    }
}

template <typename T>
GraphEvalError div_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    auto const divide = [denominator = step.parameter](T const x) -> T {
        if constexpr (std::same_as<T, uint64_t>) {
            // x / |denominator| always fits, and negating it wraps
            uint64_t const magnitude =
                denominator < 0
                    ? uint64_t{0} - static_cast<uint64_t>(denominator)
                    : static_cast<uint64_t>(denominator);
            uint64_t const quotient = x / magnitude;
            return denominator < 0 ? uint64_t{0} - quotient : quotient;
        }
        else if (denominator == -1) {
            // INT64_MIN / -1 overflows, so negate with wrapping instead
            return static_cast<T>(
                uint64_t{0} - static_cast<uint64_t>(static_cast<int64_t>(x)));
        }
        else {
            return static_cast<T>(static_cast<int64_t>(x) / denominator);
        }
    };
    run_op1<decltype(divide)>(
        chunk_at<T const>(step.inputs[0], start, arenas),
        chunk_at<T>(step.output, start, arenas),
        length,
        step.inputs[0].stride,
        divide);
    return GraphEvalError::Success;
}

// Division by 2^parameter, rounding toward zero as Div does
template <typename T>
GraphEvalError div_pow2_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    auto const shift = static_cast<unsigned>(step.parameter);
    T const *const xs = chunk_at<T const>(step.inputs[0], start, arenas);
    T *const outs = chunk_at<T>(step.output, start, arenas);
    // Every quotient is 0, and shifting by the type's width is undefined
    if (shift >= 8 * sizeof(T)) {
        std::fill_n(outs, length, T{0});
        return GraphEvalError::Success;
    }
    if constexpr (std::is_signed_v<T>) {
        // Adding 2^shift - 1 to negative values rounds toward zero
        auto const divide = [shift,
                             mask = static_cast<T>((uint64_t{1} << shift) - 1)](
                                T const x) -> T {
            return static_cast<T>((x < 0 ? x + mask : x) >> shift);
        };
        run_op1<decltype(divide)>(
            xs, outs, length, step.inputs[0].stride, divide);
    }
    else {
        auto const divide = [shift](T const x) -> T {
            return static_cast<T>(x >> shift);
        };
        run_op1<decltype(divide)>(
            xs, outs, length, step.inputs[0].stride, divide);
    }
    return GraphEvalError::Success;
}

template <typename From, typename To>
GraphEvalError saturate_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    kernel_memory_arenas &arenas = context.arenas;
    run_op1<SaturateOp::Impl<To>>(
        chunk_at<From const>(step.inputs[0], start, arenas),
        chunk_at<To>(step.output, start, arenas),
        length,
        step.inputs[0].stride);
    return GraphEvalError::Success;
}

// A whole Literal, at the op's first chunk: its elements, from the constants.
// `parameter` is their size in bytes
GraphEvalError literal_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    if (start == 0) {
        std::memcpy(
            chunk_at<uint8_t>(step.output, 0, context.arenas),
            chunk_at<uint8_t const>(step.inputs[0], 0, context.arenas),
            static_cast<size_t>(step.parameter));
    }
    return GraphEvalError::Success;
}

// A whole TensorRef, at the op's first chunk, as load_code_tensor reads it,
// with little-endian elements
GraphEvalError tensor_ref_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    if (start != 0) {
        return GraphEvalError::Success;
    }
    if (context.state == nullptr) {
        return GraphEvalError::InvalidTensorRef;
    }
    Tensor out{step.type, chunk_at<uint8_t>(step.output, 0, context.arenas)};
    return load_code_tensor(
               *context.state, step.ref, ByteOrder::LittleEndian, out)
                   .has_error()
               ? GraphEvalError::InvalidTensorRef
               : GraphEvalError::Success;
}

// A whole Concat, at the op's first chunk: `rows` blocks of a's `inner`
// bytes, then b's `columns`
GraphEvalError concat_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    if (start == 0) {
        fuse_kernels::concat(
            chunk_at<uint8_t const>(step.inputs[0], 0, context.arenas),
            chunk_at<uint8_t const>(step.inputs[1], 0, context.arenas),
            chunk_at<uint8_t>(step.output, 0, context.arenas),
            step.rows,
            step.inner,
            step.columns);
    }
    return GraphEvalError::Success;
}

// The chunk's rows of a QMatMul's product, from the same rows of x and all of
// y, x being rows of `inner` elements and y `inner` rows of `columns`
GraphEvalError qmatmul_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    uint64_t const first_row = start / step.columns;
    fuse_kernels::qmatmul(
        step.dtype,
        step.out_dtype,
        static_cast<unsigned>(step.parameter),
        chunk_at<uint8_t>(step.inputs[0], 0, context.arenas) +
            first_row * step.inner * dtype_size(step.dtype),
        chunk_at<uint8_t>(step.inputs[1], 0, context.arenas),
        chunk_at<uint8_t>(step.output, start, context.arenas),
        length / step.columns,
        step.inner,
        step.columns);
    return GraphEvalError::Success;
}

// A QMatMulEager's whole product, at the op's first chunk, as the QMatMul op
// computes it. `rows`, `inner` and `columns` are its m, k and n
GraphEvalError qmatmul_eager_step(
    FusedStep const &step, uint64_t const start, uint64_t,
    FusedContext &context)
{
    if (start == 0) {
        fuse_kernels::qmatmul(
            step.dtype,
            step.out_dtype,
            static_cast<unsigned>(step.parameter),
            chunk_at<uint8_t>(step.inputs[0], 0, context.arenas),
            chunk_at<uint8_t>(step.inputs[1], 0, context.arenas),
            chunk_at<uint8_t>(step.output, 0, context.arenas),
            step.rows,
            step.inner,
            step.columns);
    }
    return GraphEvalError::Success;
}

// The chunk's results of a ReduceSum, with WrappingAdd, or a ReduceMax, with
// Maximum: the input as blocks of `rows` rows of `inner` elements, with the
// axis running down the rows
template <typename T, typename F>
GraphEvalError reduce_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    fuse_kernels::reduce_chunk<T, F>(
        chunk_at<T const>(step.inputs[0], 0, context.arenas),
        chunk_at<T>(step.output, start, context.arenas),
        start,
        length,
        step.rows,
        step.inner);
    return GraphEvalError::Success;
}

// QMul's and QDiv's chunk, with F's `bits` fractional bits, after QDiv's
// check of its denominators
template <typename T, typename F>
GraphEvalError fixed_point_binary_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    T const *const xs =
        chunk_at<T const>(step.inputs[0], start, context.arenas);
    T const *const ys =
        chunk_at<T const>(step.inputs[1], start, context.arenas);
    if constexpr (std::same_as<F, FixedPointDiv>) {
        GraphEvalError const error = fuse_kernels::check_denominators(
            ys, step.inputs[1].stride ? length : 1);
        if (error != GraphEvalError::Success) {
            return error;
        }
    }
    run_op2(
        xs,
        ys,
        chunk_at<T>(step.output, start, context.arenas),
        length,
        step.inputs[0].stride,
        step.inputs[1].stride,
        F{static_cast<unsigned>(step.parameter)});
    return GraphEvalError::Success;
}

// QExp's and QInvSqrt's chunk, after QInvSqrt's check of its elements
template <typename T, typename F>
GraphEvalError fixed_point_unary_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    T const *const xs =
        chunk_at<T const>(step.inputs[0], start, context.arenas);
    if constexpr (std::same_as<F, FixedPointInvSqrt>) {
        GraphEvalError const error = fuse_kernels::check_inv_sqrt(
            xs, step.inputs[0].stride ? length : 1);
        if (error != GraphEvalError::Success) {
            return error;
        }
    }
    run_op1(
        xs,
        chunk_at<T>(step.output, start, context.arenas),
        length,
        step.inputs[0].stride,
        F{static_cast<unsigned>(step.parameter)});
    return GraphEvalError::Success;
}

// ISqrt's chunk, of an unsigned T
template <typename T>
GraphEvalError isqrt_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    run_op1(
        chunk_at<T const>(step.inputs[0], start, context.arenas),
        chunk_at<T>(step.output, start, context.arenas),
        length,
        step.inputs[0].stride,
        [](T const x) { return floor_sqrt(x); });
    return GraphEvalError::Success;
}

// A Gather's chunk: the data's slice at the index's one element, of `dtype`,
// which must be below `rows`, the axis's length; the slice being `inner`
// elements, broadcast to the result through `loops`
template <typename T>
GraphEvalError gather_step(
    FusedStep const &step, uint64_t const start, uint64_t const length,
    FusedContext &context)
{
    auto const index = fuse_kernels::gather_index(
        chunk_at<uint8_t const>(step.inputs[1], 0, context.arenas),
        step.dtype,
        step.rows);
    if (!index) {
        return GraphEvalError::IndexError;
    }
    fuse_kernels::broadcast_chunk(
        step.loops,
        chunk_at<T const>(step.inputs[0], 0, context.arenas) +
            *index * step.inner,
        chunk_at<T>(step.output, start, context.arenas),
        start,
        length);
    return GraphEvalError::Success;
}

// A binary instruction's step for operands of `dtype`, and its result's dtype
std::pair<StepFn, Dtype>
binary(FusedInstruction const opcode, Dtype const dtype)
{
    return visit_dtype(
        dtype, [opcode]<typename T>() -> std::pair<StepFn, Dtype> {
            switch (opcode) {
            case FusedInstruction::Add:
                return {&binary_step<T, WrappingAdd>, dtype_of<T>()};
            case FusedInstruction::Sub:
                return {&binary_step<T, WrappingSub>, dtype_of<T>()};
            case FusedInstruction::Mul:
                return {&binary_step<T, WideningMul>, dtype_of<widened_t<T>>()};
            case FusedInstruction::Max:
                return {&binary_step<T, Maximum>, dtype_of<T>()};
            case FusedInstruction::Min:
                return {&binary_step<T, Minimum>, dtype_of<T>()};
            case FusedInstruction::Greater:
                return {&binary_step<T, std::greater<>>, Dtype::uint8};
            case FusedInstruction::Ge:
                return {&binary_step<T, std::greater_equal<>>, Dtype::uint8};
            case FusedInstruction::Equal:
                return {&binary_step<T, std::equal_to<>>, Dtype::uint8};
            default:
                MONAD_ABORT();
            }
        });
}

using fuse_kernels::gather_type;
using fuse_kernels::Instruction;

// A value on the stack while an op's steps are planned
struct Value
{
    Dtype dtype;
    FusedOperand operand;
    // The chunk buffer it's in, free again once it's popped
    std::optional<uint32_t> slot;
    // The step that computes it
    std::optional<size_t> step;
};

struct Planning
{
    // Where the chunk buffers start in the region, and their size: room for
    // a chunk of the widest dtype
    uint32_t slots_offset = 0;
    uint32_t slot_bytes = 0;
    uint32_t n_slots = 0;
    std::vector<uint32_t> free_slots;
    std::vector<Value> stack;
    std::vector<FusedStep> steps;

    // A value in a chunk buffer, computed by the next step
    Value next_value(Dtype const dtype)
    {
        uint32_t slot = n_slots;
        if (free_slots.empty()) {
            n_slots++;
        }
        else {
            slot = free_slots.back();
            free_slots.pop_back();
        }
        Place const place{Arena::Region, slots_offset + slot * slot_bytes};
        return Value{dtype, FusedOperand{place, 0, true}, slot, steps.size()};
    }

    Result<Value> pop()
    {
        if (stack.empty()) {
            return GraphEvalError::GraphValidationError;
        }
        Value const value = stack.back();
        stack.pop_back();
        return value;
    }

    // A step computing a value from popped ones. Their chunk buffers are freed
    // after its own is chosen, so that it never writes over what it reads
    void push_step(
        StepFn const run, Dtype const dtype,
        std::initializer_list<Value> const inputs, int64_t const parameter = 0)
    {
        Value const value = next_value(dtype);
        FusedStep step{};
        step.run = run;
        step.parameter = parameter;
        size_t i = 0;
        for (Value const &input : inputs) {
            step.inputs[i++] = input.operand;
            if (input.slot) {
                free_slots.push_back(*input.slot);
            }
        }
        step.output = value.operand;
        steps.push_back(step);
        stack.push_back(value);
    }
};

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<void>
FusedGraph::run(std::span<uint8_t> const memory, State *const state)
{
    MONAD_ASSERT(memory.size() >= memory_size_);
    FusedContext context{
        {memory.data(),
         reinterpret_cast<uint8_t *>(constants_.data()),
         memory.data() + tensors_size_},
        state};
    for (FusedOp const &op : ops_) {
        for (uint64_t start = 0; start < op.size; start += op.chunk) {
            uint64_t const length = std::min(op.chunk, op.size - start);
            for (FusedStep const &step : op.steps) {
                GraphEvalError const error =
                    step.run(step, start, length, context);
                if (error != GraphEvalError::Success) {
                    return GraphEvalError{error};
                }
            }
        }
    }
    return outcome::success();
}

FusedGraphCompiler::FusedGraphCompiler(std::span<uint8_t const> const code)
    : code_(code)
{
}

Result<FusedGraph>
FusedGraphCompiler::compile(std::span<uint8_t const> const code)
{
    FusedGraphCompiler compiler{code};
    BOOST_OUTCOME_TRY(compiler.read_code());
    return std::move(compiler.graph_);
}

Result<Place> FusedGraphCompiler::allocate(TensorType const &type)
{
    uint64_t const offset = graph_.tensors_size_;
    if (type.size_bytes() > ARENA_SIZE - offset) {
        return GraphEvalError::OutOfMemory;
    }
    graph_.tensors_size_ =
        round_up<uint64_t>(offset + type.size_bytes(), TENSOR_DATA_ALIGNMENT);
    return Place{Arena::Memory, static_cast<uint32_t>(offset)};
}

Result<void> FusedGraphCompiler::read_code()
{
    BOOST_OUTCOME_TRY(auto const magic, read_next<uint16_t>(code_));
    if (MONAD_UNLIKELY(magic != FUSED_MAGIC)) {
        return GraphEvalError::GraphValidationError;
    }

    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code_));
    if (n_inputs > MAX_GRAPH_INPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t i = 0; i < n_inputs; i++) {
        BOOST_OUTCOME_TRY(auto const type, read_next<TensorType>(code_));
        BOOST_OUTCOME_TRY(auto const place, allocate(type));
        node_types_.push_back(type);
        node_places_.push_back(place);
        graph_.input_offsets_.push_back(place.offset);
    }

    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(code_));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(auto const output_id, read_next<uint16_t>(code_));
        outputs_.push_back(output_id);
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code_));
    for (size_t i = 0; i < n_ops; i++) {
        BOOST_OUTCOME_TRY(read_op());
    }
    if (!code_.empty()) {
        return GraphEvalError::GraphValidationError;
    }

    for (size_t const id : outputs_) {
        if (id >= node_places_.size()) {
            return GraphEvalError::GraphValidationError;
        }
        graph_.output_offsets_.push_back(node_places_[id].offset);
    }
    graph_.memory_size_ = graph_.tensors_size_ + region_size_;
    if (graph_.memory_size_ > ARENA_SIZE) {
        return GraphEvalError::OutOfMemory;
    }
    return outcome::success();
}

Result<void> FusedGraphCompiler::read_op()
{
    BOOST_OUTCOME_TRY(
        auto const op_core, fuse_kernels::read_core(code_, node_types_));
    FusedCore const core = op_core.core;
    auto const &core_inputs = op_core.inputs;
    auto const &core_type = op_core.type;
    uint8_t const axis = op_core.axis;
    BOOST_OUTCOME_TRY(
        auto const instructions,
        fuse_kernels::read_instructions(
            code_, node_types_.size(), core != FusedCore::Map));
    if (core == FusedCore::Reshape) {
        if (!instructions.empty()) {
            return GraphEvalError::GraphValidationError;
        }
        Place const place = node_places_[core_inputs[0]];
        node_types_.push_back(*core_type);
        node_places_.push_back(place);
        return outcome::success();
    }

    // The shapes the result's is broadcast from: the core's, then the Inputs'
    std::vector<Shape> shapes;
    if (core_type) {
        shapes.push_back(core_type->shape());
    }
    for (Instruction const &instruction : instructions) {
        if (instruction.opcode == FusedInstruction::Input) {
            shapes.push_back(node_types_[instruction.input_id].shape());
        }
        if (instruction.opcode == FusedInstruction::Gather) {
            BOOST_OUTCOME_TRY(
                auto const type, gather_type(node_types_, instruction));
            shapes.push_back(type.shape());
        }
    }
    BOOST_OUTCOME_TRY(auto const shape, broadcast_shape(shapes));
    if (core_type && shape != shapes[0]) {
        return GraphEvalError::ShapeError;
    }
    uint64_t const size = shape.size();

    uint64_t chunk = FUSED_CHUNK;
    if (core == FusedCore::MatMul || core == FusedCore::QMatMul) {
        uint64_t const columns = std::max<uint64_t>(shape.dimensions()[1], 1);
        chunk = std::max<uint64_t>(FUSED_CHUNK / columns, 1) * columns;
    }
    Planning planning;
    planning.slot_bytes = static_cast<uint32_t>(chunk * sizeof(uint64_t));
    std::optional<Value> core_value;
    if (core_type) {
        Dtype const dtype = core_type->dtype();
        // A Literal and a TensorRef have no input nodes
        auto const input_type = [&](size_t const i) -> TensorType const & {
            return node_types_[core_inputs[i]];
        };
        auto const input_place = [&](size_t const i) {
            return node_places_[core_inputs[i]];
        };
        FusedStep step{};
        if (core == FusedCore::Literal) {
            // Its elements, in the constants, from a uint64_t of their own
            auto const offset = static_cast<uint32_t>(
                graph_.constants_.size() * sizeof(uint64_t));
            graph_.constants_.resize(
                graph_.constants_.size() +
                (op_core.literal.size() + sizeof(uint64_t) - 1) /
                    sizeof(uint64_t));
            if (!op_core.literal.empty()) {
                std::memcpy(
                    reinterpret_cast<uint8_t *>(graph_.constants_.data()) +
                        offset,
                    op_core.literal.data(),
                    op_core.literal.size());
            }
            step.run = &literal_step;
            step.inputs[0] =
                FusedOperand{Place{Arena::Literals, offset}, 0, true};
            step.parameter = static_cast<int64_t>(op_core.literal.size());
        }
        else if (core == FusedCore::TensorRef) {
            step.run = &tensor_ref_step;
            step.ref = op_core.ref;
            step.type = *core_type;
        }
        else if (
            core == FusedCore::QMatMul || core == FusedCore::QMatMulEager) {
            step.run = core == FusedCore::QMatMul ? &qmatmul_step
                                                  : &qmatmul_eager_step;
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.inputs[1] = FusedOperand{input_place(1), 0, true};
            step.rows = shape.dimensions()[0];
            step.inner = input_type(0).shape().dimensions()[1];
            step.columns = shape.dimensions()[1];
            step.dtype = input_type(0).dtype();
            step.out_dtype = dtype;
            step.parameter = op_core.bits;
        }
        else if (core == FusedCore::ReduceSum || core == FusedCore::ReduceMax) {
            Shape const &in = input_type(0).shape();
            bool const sum = core == FusedCore::ReduceSum;
            step.run = visit_dtype(dtype, [sum]<typename T>() -> StepFn {
                return sum ? &reduce_step<T, WrappingAdd>
                           : &reduce_step<T, Maximum>;
            });
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.rows = in.dimensions()[axis];
            step.inner = dimensions_product(in, axis + 1u, in.rank());
        }
        else if (core == FusedCore::Concat) {
            Shape const &a = input_type(0).shape();
            Shape const &b = input_type(1).shape();
            uint64_t const inner =
                dimensions_product(a, axis + 1u, a.rank()) * dtype_size(dtype);
            step.run = &concat_step;
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.inputs[1] = FusedOperand{input_place(1), 0, true};
            step.rows = dimensions_product(a, 0, axis);
            step.inner = a.dimensions()[axis] * inner;
            step.columns = b.dimensions()[axis] * inner;
        }
        else if (core == FusedCore::CumSum) {
            Place const x_place = input_place(0);
            uint64_t inner = 1;
            for (size_t i = axis + 1u; i < shape.rank(); i++) {
                inner *= shape.dimensions()[i];
            }
            // The row of running sums goes before the chunk buffers
            planning.slots_offset = static_cast<uint32_t>(round_up<uint64_t>(
                inner * dtype_size(dtype), TENSOR_DATA_ALIGNMENT));
            step.run = visit_dtype(
                dtype, []<typename T>() -> StepFn { return &cumsum_step<T>; });
            step.inputs[0] = FusedOperand{
                x_place, static_cast<uint32_t>(dtype_size(dtype)), true};
            step.inputs[1] = FusedOperand{Place{Arena::Region, 0}, 0, true};
            step.rows = shape.dimensions()[axis];
            step.inner = inner;
        }
        else if (core == FusedCore::MatMul) {
            step.run = &matmul_step;
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.inputs[1] = FusedOperand{input_place(1), 0, true};
            step.inner = input_type(0).shape().dimensions()[1];
            step.columns = shape.dimensions()[1];
        }
        else if (core == FusedCore::MatMulEager) {
            step.run = &matmul_eager_step;
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.inputs[1] = FusedOperand{input_place(1), 0, true};
            step.rows = shape.dimensions()[0];
            step.inner = input_type(0).shape().dimensions()[1];
            step.columns = shape.dimensions()[1];
        }
        else if (core == FusedCore::Gather) {
            step.run = &gather_core_step;
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.inputs[1] = FusedOperand{input_place(1), 0, true};
            step.parameter = axis;
            step.input_type = input_type(0);
            step.index_type = input_type(1);
            step.type = *core_type;
        }
        else if (StepFn const run = eager_op_step_for(core)) {
            step.run = run;
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.parameter = axis;
            step.input_type = input_type(0);
            step.type = *core_type;
        }
        else {
            step.run = visit_dtype(
                dtype, []<typename T>() -> StepFn { return &argmax_step<T>; });
            step.inputs[0] = FusedOperand{input_place(0), 0, true};
            step.inner = input_type(0).shape().size();
        }
        if (is_whole_core(core)) {
            // The whole core, in memory of its own, which the instructions
            // read as they read a tensor
            BOOST_OUTCOME_TRY(auto const product, allocate(*core_type));
            core_value = Value{
                dtype,
                FusedOperand{
                    product, static_cast<uint32_t>(dtype_size(dtype)), true},
                std::nullopt,
                planning.steps.size()};
        }
        else {
            core_value = planning.next_value(dtype);
            // Core can be pushed any number of times, so its buffer stays
            // taken
            core_value->slot.reset();
        }
        step.output = core_value->operand;
        planning.steps.push_back(step);
    }

    for (Instruction const &instruction : instructions) {
        switch (instruction.opcode) {
        case FusedInstruction::Core:
            planning.stack.push_back(*core_value);
            break;
        case FusedInstruction::Input: {
            TensorType const &type = node_types_[instruction.input_id];
            Place const place = node_places_[instruction.input_id];
            uint64_t const n = type.shape().size();
            if (n == size || n == 1) {
                auto const advance =
                    n == size ? static_cast<uint32_t>(dtype_size(type.dtype()))
                              : uint32_t{0};
                planning.stack.push_back(Value{
                    type.dtype(),
                    FusedOperand{place, advance, n == size},
                    std::nullopt,
                    std::nullopt});
                break;
            }
            BOOST_OUTCOME_TRY(
                auto const loops, broadcast<2>({shape, type.shape()}));
            Value const value = planning.next_value(type.dtype());
            FusedStep step{};
            step.run = visit_dtype(type.dtype(), []<typename T>() -> StepFn {
                return &broadcast_step<T>;
            });
            step.inputs[0] = FusedOperand{place, 0, true};
            step.output = value.operand;
            step.loops = loops;
            planning.steps.push_back(step);
            planning.stack.push_back(value);
            break;
        }
        case FusedInstruction::Constant: {
            Place const place{
                Arena::Literals,
                static_cast<uint32_t>(
                    graph_.constants_.size() * sizeof(uint64_t))};
            graph_.constants_.push_back(instruction.constant);
            planning.stack.push_back(Value{
                instruction.dtype,
                FusedOperand{place, 0, false},
                std::nullopt,
                std::nullopt});
            break;
        }
        case FusedInstruction::Gather: {
            BOOST_OUTCOME_TRY(
                auto const type, gather_type(node_types_, instruction));
            BOOST_OUTCOME_TRY(
                auto const loops, broadcast<2>({shape, type.shape()}));
            Shape const &data = node_types_[instruction.input_id].shape();
            Value const value = planning.next_value(type.dtype());
            FusedStep step{};
            step.run = visit_dtype(type.dtype(), []<typename T>() -> StepFn {
                return &gather_step<T>;
            });
            step.inputs[0] =
                FusedOperand{node_places_[instruction.input_id], 0, true};
            step.inputs[1] =
                FusedOperand{node_places_[instruction.index_id], 0, true};
            step.output = value.operand;
            step.loops = loops;
            step.rows = data.dimensions()[instruction.axis];
            step.inner =
                dimensions_product(data, instruction.axis + 1u, data.rank());
            step.dtype = node_types_[instruction.index_id].dtype();
            planning.steps.push_back(step);
            planning.stack.push_back(value);
            break;
        }
        case FusedInstruction::QMul:
        case FusedInstruction::QDiv: {
            BOOST_OUTCOME_TRY(auto const y, planning.pop());
            BOOST_OUTCOME_TRY(auto const x, planning.pop());
            if (x.dtype != y.dtype) {
                return GraphEvalError::TypeError;
            }
            bool const mul = instruction.opcode == FusedInstruction::QMul;
            auto const run =
                visit_dtype(x.dtype, [mul]<typename T>() -> StepFn {
                    return mul ? &fixed_point_binary_step<T, FixedPointMul>
                               : &fixed_point_binary_step<T, FixedPointDiv>;
                });
            planning.push_step(run, x.dtype, {x, y}, instruction.parameter);
            break;
        }
        case FusedInstruction::QExp:
        case FusedInstruction::QInvSqrt: {
            BOOST_OUTCOME_TRY(auto const x, planning.pop());
            bool const exp = instruction.opcode == FusedInstruction::QExp;
            auto const run =
                visit_dtype(x.dtype, [exp]<typename T>() -> StepFn {
                    return exp ? &fixed_point_unary_step<T, FixedPointExp>
                               : &fixed_point_unary_step<T, FixedPointInvSqrt>;
                });
            planning.push_step(run, x.dtype, {x}, instruction.parameter);
            break;
        }
        case FusedInstruction::ISqrt: {
            BOOST_OUTCOME_TRY(auto const x, planning.pop());
            if (dtype_signed(x.dtype)) {
                return GraphEvalError::TypeError;
            }
            auto const run = visit_dtype(x.dtype, []<typename T>() -> StepFn {
                if constexpr (std::is_unsigned_v<T>) {
                    return &isqrt_step<T>;
                }
                else {
                    // Signed dtypes are rejected above
                    MONAD_ABORT();
                }
            });
            planning.push_step(run, x.dtype, {x});
            break;
        }
        case FusedInstruction::Sub:
        case FusedInstruction::Greater:
        case FusedInstruction::Ge:
        case FusedInstruction::Equal:
        case FusedInstruction::Add:
        case FusedInstruction::Mul:
        case FusedInstruction::Max:
        case FusedInstruction::Min: {
            BOOST_OUTCOME_TRY(auto const y, planning.pop());
            BOOST_OUTCOME_TRY(auto const x, planning.pop());
            if (x.dtype != y.dtype) {
                return GraphEvalError::TypeError;
            }
            auto const [run, dtype] = binary(instruction.opcode, x.dtype);
            planning.push_step(run, dtype, {x, y});
            break;
        }
        case FusedInstruction::Div: {
            BOOST_OUTCOME_TRY(auto const x, planning.pop());
            int64_t const denominator = instruction.parameter;
            bool const power_of_two =
                denominator > 0 &&
                std::has_single_bit(static_cast<uint64_t>(denominator));
            auto const run =
                visit_dtype(x.dtype, [power_of_two]<typename T>() -> StepFn {
                    return power_of_two ? &div_pow2_step<T> : &div_step<T>;
                });
            planning.push_step(
                run,
                x.dtype,
                {x},
                power_of_two
                    ? std::countr_zero(static_cast<uint64_t>(denominator))
                    : denominator);
            break;
        }
        case FusedInstruction::Saturate: {
            BOOST_OUTCOME_TRY(auto const x, planning.pop());
            auto const run = visit_dtype(x.dtype, [&]<typename From>() {
                return visit_dtype(
                    instruction.dtype, []<typename To>() -> StepFn {
                        return &saturate_step<From, To>;
                    });
            });
            planning.push_step(run, instruction.dtype, {x});
            break;
        }
        case FusedInstruction::Where: {
            BOOST_OUTCOME_TRY(auto const y, planning.pop());
            BOOST_OUTCOME_TRY(auto const x, planning.pop());
            BOOST_OUTCOME_TRY(auto const condition, planning.pop());
            if (condition.dtype != Dtype::uint8 || x.dtype != y.dtype) {
                return GraphEvalError::TypeError;
            }
            auto const run = visit_dtype(
                x.dtype, []<typename T>() -> StepFn { return &where_step<T>; });
            planning.push_step(run, x.dtype, {condition, x, y});
            break;
        }
        }
    }
    if (planning.stack.size() != 1) {
        return GraphEvalError::GraphValidationError;
    }

    Value const &result = planning.stack.back();
    BOOST_OUTCOME_TRY(
        auto const type, TensorType::checked(result.dtype, shape));
    BOOST_OUTCOME_TRY(auto const place, allocate(type));
    FusedOperand const output{
        place, static_cast<uint32_t>(dtype_size(result.dtype)), true};
    // The last step computes the result, and writes it in place of a chunk
    // buffer, unless the result is a tensor or a constant to copy
    if (result.step && *result.step + 1 == planning.steps.size()) {
        planning.steps.back().output = output;
    }
    else {
        FusedStep step{};
        step.run = visit_dtype(
            result.dtype, []<typename T>() -> StepFn { return &copy_step<T>; });
        step.inputs[0] = result.operand;
        step.output = output;
        planning.steps.push_back(step);
    }

    node_types_.push_back(type);
    node_places_.push_back(place);
    graph_.ops_.push_back(
        FusedGraph::FusedOp{size, chunk, std::move(planning.steps)});
    region_size_ = std::max(
        region_size_,
        planning.slots_offset +
            uint64_t{planning.n_slots} * planning.slot_bytes);
    return outcome::success();
}

MONAD_GRAPH_EVAL_NAMESPACE_END
