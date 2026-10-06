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

#include "category/execution/monad/graph_eval/broadcasting.hpp"
#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/kernel.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include <type_traits>
#include <utility>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

template <size_t N>
using InputTypes = std::array<TensorType const *, N>;

template <size_t N>
using Inputs = std::array<Tensor const *, N>;

// Base for graph ops with `Arity` input tensors. After its opcode, an op's
// graphcode holds its parameters, as read by `read_next<Parameters>`, then one
// uint16 node index per input. A node index names a graph input or an earlier
// op's result, so inputs can only refer backwards. A derived op computes its
// result from the loaded parameters and inputs in `evaluate`, into `output`,
// which is already allocated. `check` works out the type of that result from
// the inputs' types, without computing it. An op without parameters uses
// std::monostate.
template <typename Parameters, size_t Arity>
struct GraphOp
{
    virtual Result<void> evaluate_impl(
        Parameters params, Tensor &output, Inputs<Arity> const &inputs) = 0;

    virtual Result<TensorType>
    check_impl(Parameters params, InputTypes<Arity> const &input_types) = 0;

    Result<void> evaluate(
        std::span<uint8_t const> &graphcode, Tensor &output,
        std::vector<Tensor> const &node_values)
    {
        BOOST_OUTCOME_TRY(auto const params, read_next<Parameters>(graphcode));

        std::array<Tensor const *, Arity> inputs{};
        for (auto &input : inputs) {
            BOOST_OUTCOME_TRY(
                auto const node_id, read_next<uint16_t>(graphcode));
            if (node_id >= node_values.size()) {
                return GraphEvalError::GraphValidationError;
            }
            input = &node_values[node_id];
        }

        return evaluate_impl(params, output, inputs);
    }

    // Also replaces `input_ids` with the node ids of the op's inputs. TODO:
    // make it so we don't need the input_ids hack
    Result<TensorType> check(
        std::span<uint8_t const> &graphcode,
        std::vector<TensorType> const &node_types,
        std::vector<uint16_t> &input_ids)
    {
        BOOST_OUTCOME_TRY(auto const params, read_next<Parameters>(graphcode));

        input_ids.clear();
        std::array<TensorType const *, Arity> input_types{};
        for (auto &input : input_types) {
            BOOST_OUTCOME_TRY(
                auto const node_id, read_next<uint16_t>(graphcode));
            if (node_id >= node_types.size()) {
                return GraphEvalError::GraphValidationError;
            }
            input = &node_types[node_id];
            input_ids.push_back(node_id);
        }

        return check_impl(params, input_types);
    }

protected:
    ~GraphOp() = default;
};

// Literal: a constant tensor, copied out of the graphcode
struct LiteralOp final
    : GraphOp<std::tuple<TensorType, std::span<uint8_t const>>, 0>
{

    Result<TensorType> check_impl(
        std::tuple<TensorType, std::span<uint8_t const>> params,
        InputTypes<0> const &) override
    {
        auto const &[type, bytes] = params;
        if (type.size_bytes() != bytes.size_bytes()) {
            return GraphEvalError::GraphValidationError;
        }
        return type;
    }

    Result<void> evaluate_impl(
        std::tuple<TensorType, std::span<uint8_t const>> const params,
        Tensor &output, Inputs<0> const &) override
    {
        auto const &[type, data] = params;
        std::memcpy(output.data(), data.data(), data.size());
        return outcome::success();
    }
};

// TODO: abstract over run_opN with template metaprogramming
template <typename F, typename T, typename Out>
[[gnu::always_inline]]
inline void run_op1(
    T const *__restrict const xs, Out *__restrict const outs,
    uint64_t const length, bool const x_stride)
{
    if (x_stride) {
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(F{}(xs[i]));
        }
    }
    else {
        auto const out = static_cast<Out>(F{}(xs[0]));
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = out;
        }
    }
}

template <typename F, typename XT, typename YT, typename Out>
[[gnu::always_inline]]
inline void run_op2(
    XT const *__restrict const xs, YT const *__restrict const ys,
    Out *__restrict const outs, uint64_t const length, bool const x_stride,
    bool const y_stride)
{
    if (x_stride && y_stride) {
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(F{}(xs[i], ys[i]));
        }
    }
    else if (x_stride) {
        YT const y = ys[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(F{}(xs[i], y));
        }
    }
    else if (y_stride) {
        XT const x = xs[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(F{}(x, ys[i]));
        }
    }
    else {
        auto const out = static_cast<Out>(F{}(xs[0], ys[0]));
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = out;
        }
    }
}

template <typename F, typename XT, typename YT, typename ZT, typename Out>
[[gnu::always_inline]]
inline void run_op3(
    XT const *__restrict const xs, YT const *__restrict const ys,
    ZT const *__restrict const zs, Out *__restrict const outs,
    uint64_t const length, bool const x_stride, bool const y_stride,
    bool const z_stride)
{
#define INNER_LOOP_F(x, y, z)                                                  \
    for (size_t i = 0; i < length; i++) {                                      \
        outs[i] = static_cast<Out>(F{}(x, y, z));                              \
    }
    if (!x_stride) {
        auto const x = xs[0];
        if (!y_stride) {
            auto const y = ys[0];
            if (!z_stride) {
                auto const z = zs[0];
                auto const out = static_cast<Out>(F{}(x, y, z));
                for (size_t i = 0; i < length; i++) {
                    outs[i] = out;
                }
            }
            else {
                INNER_LOOP_F(x, y, zs[i]);
            }
        }
        else {
            if (!z_stride) {
                auto const z = zs[0];
                INNER_LOOP_F(x, ys[i], z);
            }
            else {
                INNER_LOOP_F(x, ys[i], zs[i]);
            }
        }
    }
    else {
        if (!y_stride) {
            auto const y = ys[0];
            if (!z_stride) {
                auto const z = zs[0];
                INNER_LOOP_F(xs[i], y, z);
            }
            else {
                INNER_LOOP_F(xs[i], y, zs[i]);
            }
        }
        else {
            if (!z_stride) {
                auto const z = zs[0];
                INNER_LOOP_F(xs[i], ys[i], z);
            }
            else {
                INNER_LOOP_F(xs[i], ys[i], zs[i]);
            }
        }
    }
#undef INNER_LOOP_F
}

// Applies F element by element to two tensors of the same dtype, with their
// shapes broadcast together. The output has the broadcast shape, and the dtype
// of what F returns, with bool stored as uint8 0/1.
template <typename F>
struct ElementwiseOp2 final : GraphOp<std::monostate, 2>
{
    // The output's element type for inputs of T
    template <typename T>
    using Out = std::conditional_t<
        std::same_as<std::invoke_result_t<F, T, T>, bool>, uint8_t,
        std::invoke_result_t<F, T, T>>;

    Result<TensorType>
    check_impl(std::monostate, InputTypes<2> const &input_types) override
    {
        TensorType const &x = *input_types[0];
        TensorType const &y = *input_types[1];
        if (x.dtype != y.dtype) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const shape, broadcast_shape(std::array{x.shape, y.shape}));
        Dtype const dtype = visit_dtype(
            x.dtype, []<typename T>() { return dtype_of<Out<T>>(); });
        return TensorType{dtype, shape};
    }

    Result<void> evaluate_impl(
        std::monostate, Tensor &output, Inputs<2> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        Tensor const &y = *inputs[1];
        if (x.type().dtype != y.type().dtype) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const loops, broadcast<2>({x.type().shape, y.type().shape}));

        return visit_dtype(x.type().dtype, [&]<typename T>() -> Result<void> {
            T const *const xs = x.elements<T const>().data();
            T const *const ys = y.elements<T const>().data();
            Out<T> *const outs = output.template elements<Out<T>>().data();
            for_each_run(
                loops,
                [&](auto const &offsets,
                    uint64_t start,
                    uint64_t length,
                    auto const &strides) {
                    run_op2<F>(
                        xs + offsets[0],
                        ys + offsets[1],
                        outs + start,
                        length,
                        strides[0],
                        strides[1]);
                });
            return outcome::success();
        });
    }
};

// Two's complement wrapping arithmetic, without the UB of signed overflow
struct WrappingAdd
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        T result{};
        (void)__builtin_add_overflow(a, b, &result);
        return result;
    }
};

struct WrappingSub
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        T result{};
        (void)__builtin_sub_overflow(a, b, &result);
        return result;
    }
};

// Products in the type twice as wide, where they're exact; 64-bit products
// stay 64-bit and wrap, like Add's sums
struct WideningMul
{
    template <typename T>
    widened_t<T> operator()(T const a, T const b) const
    {
        using Wide = widened_t<T>;
        Wide result{};
        (void)__builtin_mul_overflow(
            static_cast<Wide>(a), static_cast<Wide>(b), &result);
        return result;
    }
};

using AddOp = ElementwiseOp2<WrappingAdd>;
using SubOp = ElementwiseOp2<WrappingSub>;

using GreaterOp = ElementwiseOp2<std::greater<>>;

using GeOp = ElementwiseOp2<std::greater_equal<>>;
using EqualOp = ElementwiseOp2<std::equal_to<>>;
using MulOp = ElementwiseOp2<WideningMul>;

struct Maximum
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        return a < b ? b : a;
    }
};

struct Minimum
{
    template <typename T>
    T operator()(T const a, T const b) const
    {
        return b < a ? b : a;
    }
};

using MaxOp = ElementwiseOp2<Maximum>;
using MinOp = ElementwiseOp2<Minimum>;

// Reshape: the input's elements under a new shape with the same element count.
// The result shares the input's data, which is safe while tensors are never
// written after they're produced
struct ReshapeOp final : GraphOp<Shape, 1>
{

    Result<TensorType>
    check_impl(Shape const shape, InputTypes<1> const &input_types) override
    {
        TensorType const &x = *input_types[0];
        if (shape.size() != x.shape.size()) {
            return GraphEvalError::ShapeError;
        }
        return TensorType{x.dtype, shape};
    }

    Result<void> evaluate_impl(
        Shape const shape, Tensor &out, Inputs<1> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        (void)out;
        if (shape.size() != x.type().shape.size()) {
            return GraphEvalError::ShapeError;
        }
        return outcome::success();
    }
};

// Where: each element from x where the condition is nonzero, else from y, with
// the three shapes broadcast together. The condition is uint8, as comparisons
// return.
struct WhereOp final : GraphOp<std::monostate, 3>
{

    template <typename T>
    struct Impl
    {
        T operator()(bool const cond, T const left, T const right) const
        {
            return cond ? left : right;
        }
    };

    Result<TensorType>
    check_impl(std::monostate, InputTypes<3> const &input_types) override
    {
        TensorType const &condition = *input_types[0];
        TensorType const &x = *input_types[1];
        TensorType const &y = *input_types[2];
        if (condition.dtype != Dtype::uint8 || x.dtype != y.dtype) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const shape,
            broadcast_shape(std::array{condition.shape, x.shape, y.shape}));
        return TensorType{x.dtype, shape};
    }

    Result<void>
    evaluate_impl(std::monostate, Tensor &out, Inputs<3> const &inputs) override
    {
        Tensor const &condition = *inputs[0];
        Tensor const &x = *inputs[1];
        Tensor const &y = *inputs[2];
        if (condition.type().dtype != Dtype::uint8 ||
            x.type().dtype != y.type().dtype) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<3>(
                {condition.type().shape, x.type().shape, y.type().shape}));

        visit_dtype(x.type().dtype, [&]<typename T>() {
            uint8_t const *const conditions =
                condition.elements<uint8_t const>().data();
            T const *const xs = x.elements<T const>().data();
            T const *const ys = y.elements<T const>().data();
            T *const outs = out.elements<T>().data();
            for_each_run(
                loops,
                [&](auto const &offsets,
                    uint64_t start,
                    uint64_t length,
                    auto const &strides) {
                    run_op3<Impl<T>>(
                        conditions + offsets[0],
                        xs + offsets[1],
                        ys + offsets[2],
                        outs + start,
                        length,
                        strides[0],
                        strides[1],
                        strides[2]);
                });
        });
        return outcome::success();
    }
};

// Saturate: converts to the dtype given as its parameter, clamping values
// outside that dtype's range to the nearest bound
struct SaturateOp final : GraphOp<Dtype, 1>
{

    Result<TensorType>
    check_impl(Dtype const dtype, InputTypes<1> const &input_types) override
    {
        return TensorType{dtype, input_types[0]->shape};
    }

    Result<void> evaluate_impl(
        Dtype const dtype, Tensor &out, Inputs<1> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        visit_dtype(x.type().dtype, [&]<typename From>() {
            visit_dtype(dtype, [&]<typename To>() {
                auto const xs = x.elements<From const>();
                auto const outs = out.elements<To>();
                for (size_t i = 0; i < outs.size(); i++) {
                    if (std::cmp_less(xs[i], std::numeric_limits<To>::min())) {
                        outs[i] = std::numeric_limits<To>::min();
                    }
                    else if (std::cmp_greater(
                                 xs[i], std::numeric_limits<To>::max())) {
                        outs[i] = std::numeric_limits<To>::max();
                    }
                    else {
                        outs[i] = static_cast<To>(
                            xs[i]); // NOLINT(bugprone-signed-char-misuse)
                    }
                }
            });
        });
        return outcome::success();
    }
};

// Expand: broadcasts the input to the shape given as its parameter, as
// numpy.broadcast_to does. The input's dimensions are matched against the
// shape's last ones, and each must equal its counterpart or be 1, in which case
// the input is repeated along it. Element-wise ops broadcast their operands
// themselves, so this is only needed for a broadcast tensor on its own.
struct ExpandOp final : GraphOp<Shape, 1>
{

    template <typename T>
    struct Impl
    {
        T operator()(T const x) const
        {
            return x;
        }
    };

    Result<TensorType>
    check_impl(Shape const shape, InputTypes<1> const &input_types) override
    {
        TensorType const &x = *input_types[0];
        if (x.shape.rank > shape.rank) {
            return GraphEvalError::RankError;
        }
        BOOST_OUTCOME_TRY(
            auto const broadcast, broadcast_shape(std::array{shape, x.shape}));
        if (!same_shape(broadcast, shape)) {
            return GraphEvalError::ShapeError;
        }
        return TensorType{x.dtype, shape};
    }

    Result<void> evaluate_impl(
        Shape const shape, Tensor &out, Inputs<1> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        if (x.type().shape.rank > shape.rank) {
            return GraphEvalError::RankError;
        }
        // Broadcasting the input against the shape gives back the shape
        // exactly when each of the input's dimensions matches it or is 1
        BOOST_OUTCOME_TRY(
            auto const loops, broadcast<2>({shape, x.type().shape}));
        if (!same_shape(loops.shape, shape)) {
            return GraphEvalError::ShapeError;
        }

        visit_dtype(x.type().dtype, [&]<typename T>() {
            T const *const xs = x.elements<T const>().data();
            T *const outs = out.elements<T>().data();
            for_each_run(
                loops,
                [&](auto const &offsets,
                    uint64_t start,
                    uint64_t length,
                    auto const &strides) {
                    run_op1<Impl<T>>(
                        xs + offsets[1], outs + start, length, strides[1]);
                });
        });
        return outcome::success();
    }
};

// Div: divides each element by the denominator given as its parameter, an
// int64 that must be nonzero, as `divide` does
struct DivOp final : GraphOp<int64_t, 1>
{

    Result<TensorType> check_impl(
        int64_t const denominator, InputTypes<1> const &input_types) override
    {
        if (denominator == 0) {
            return GraphEvalError::GraphValidationError;
        }
        return *input_types[0];
    }

    Result<void> evaluate_impl(
        int64_t const denominator, Tensor &out,
        Inputs<1> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        if (denominator == 0) {
            return GraphEvalError::GraphValidationError;
        }
        visit_dtype(x.type().dtype, [&]<typename T>() {
            auto const xs = x.elements<T const>();
            auto const outs = out.elements<T>();
            for (size_t i = 0; i < outs.size(); i++) {
                if constexpr (std::same_as<T, uint64_t>) {
                    // x / |denominator| always fits, and negating it wraps
                    uint64_t const magnitude =
                        denominator < 0
                            ? uint64_t{0} - static_cast<uint64_t>(denominator)
                            : static_cast<uint64_t>(denominator);
                    uint64_t const quotient = xs[i] / magnitude;
                    outs[i] =
                        denominator < 0 ? uint64_t{0} - quotient : quotient;
                }
                else {
                    // Every other T fits in int64
                    if (denominator == -1) {
                        outs[i] = static_cast<T>(
                            uint64_t{0} -
                            static_cast<uint64_t>(static_cast<int64_t>(xs[i])));
                    }
                    else {
                        outs[i] = static_cast<T>(
                            static_cast<int64_t>(xs[i]) / denominator);
                    }
                }
            }
        });
        return outcome::success();
    }
};

// MatMul: the product of two int8 matrices, in int32, which can't overflow:
// even 65535 products of -128 and -128 sum to less than 2^31
struct MatMulOp final : GraphOp<std::monostate, 2>
{

    Result<TensorType>
    check_impl(std::monostate, InputTypes<2> const &input_types) override
    {
        TensorType const &x = *input_types[0];
        TensorType const &y = *input_types[1];
        if (x.dtype != Dtype::int8 || y.dtype != Dtype::int8) {
            return GraphEvalError::TypeError;
        }
        if (x.shape.rank != 2 || y.shape.rank != 2) {
            return GraphEvalError::RankError;
        }
        if (y.shape.dimensions[0] != x.shape.dimensions[1]) {
            return GraphEvalError::ShapeError;
        }
        return TensorType{
            Dtype::int32,
            Shape{2, {x.shape.dimensions[0], y.shape.dimensions[1]}}};
    }

    Result<void>
    evaluate_impl(std::monostate, Tensor &out, Inputs<2> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        Tensor const &y = *inputs[1];
        if (x.type().dtype != Dtype::int8 || y.type().dtype != Dtype::int8) {
            return GraphEvalError::TypeError;
        }
        // TODO: support batched matmul
        if (x.type().shape.rank != 2 || y.type().shape.rank != 2) {
            return GraphEvalError::RankError;
        }
        uint16_t const m = x.type().shape.dimensions[0];
        uint16_t const k = x.type().shape.dimensions[1];
        uint16_t const n = y.type().shape.dimensions[1];
        if (y.type().shape.dimensions[0] != k) {
            return GraphEvalError::ShapeError;
        }

        // An empty output needs no computing, and keeps zero-size buffers
        // from IREE
        if (m != 0 && n != 0) {
            std::vector<Tensor> inputs{x, y};
            Kernel("module.matmul_i8")(inputs, out);
        }
        return outcome::success();
    }
};

// ArgMax: the row-major index of the input's largest element, the first of any
// equal ones, as a scalar of the input's dtype, so an index that doesn't fit
// wraps. An empty input has none.
struct ArgMaxOp final : GraphOp<std::monostate, 1>
{

    Result<TensorType>
    check_impl(std::monostate, InputTypes<1> const &input_types) override
    {
        TensorType const &x = *input_types[0];
        if (x.shape.size() == 0) {
            return GraphEvalError::ShapeError;
        }
        return TensorType{x.dtype, Shape{}};
    }

    Result<void>
    evaluate_impl(std::monostate, Tensor &out, Inputs<1> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        if (x.type().shape.size() == 0) {
            return GraphEvalError::ShapeError;
        }
        visit_dtype(x.type().dtype, [&]<typename T>() {
            auto const xs = x.elements<T const>();
            size_t largest = 0;
            for (size_t i = 1; i < xs.size(); i++) {
                if (xs[largest] < xs[i]) {
                    largest = i;
                }
            }
            out.elements<T>()[0] = static_cast<T>(largest);
        });
        return outcome::success();
    }
};

// CumSum: running sums along the axis given as its parameter, inclusive and in
// increasing index order, wrapping on overflow like Add
struct CumSumOp final : GraphOp<uint8_t, 1>
{
    Result<TensorType>
    check_impl(uint8_t const axis, InputTypes<1> const &input_types) override
    {
        TensorType const &x = *input_types[0];
        if (axis >= x.shape.rank) {
            return GraphEvalError::RankError;
        }
        return x;
    }

    Result<void> evaluate_impl(
        uint8_t const axis, Tensor &out, Inputs<1> const &inputs) override
    {
        Tensor const &x = *inputs[0];
        if (axis >= x.type().shape.rank) {
            return GraphEvalError::RankError;
        }

        // The input as `outer` blocks of `length` rows of `inner` elements,
        // with the axis running down the rows
        uint64_t outer = 1;
        for (size_t i = 0; i < axis; i++) {
            outer *= x.type().shape.dimensions[i];
        }
        uint64_t const length = x.type().shape.dimensions[axis];
        uint64_t inner = 1;
        for (size_t i = axis + 1u; i < x.type().shape.rank; i++) {
            inner *= x.type().shape.dimensions[i];
        }

        visit_dtype(x.type().dtype, [&]<typename T>() {
            auto const xs = x.elements<T const>();
            auto const outs = out.elements<T>();
            for (uint64_t block = 0; block < outer; block++) {
                for (uint64_t row = 0; row < length; row++) {
                    uint64_t const start = (block * length + row) * inner;
                    for (uint64_t i = start; i < start + inner; i++) {
                        outs[i] = row == 0
                                      ? xs[i]
                                      : WrappingAdd{}(outs[i - inner], xs[i]);
                    }
                }
            }
        });
        return outcome::success();
    }
};

MONAD_GRAPH_EVAL_NAMESPACE_END
