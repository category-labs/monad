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
#include "category/execution/monad/graph_eval/broadcasting.hpp"
#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/constants.hpp"
#include "category/execution/monad/graph_eval/fixed_point.hpp"
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/matmul.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include <algorithm>
#include <cstring>
#include <limits>
#include <span>
#include <tuple>
#include <type_traits>
#include <utility>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

template <size_t Arity>
using InputTypes = std::array<TensorType const *, Arity>;

template <size_t Arity>
using InputValues = std::array<Tensor const *, Arity>;

template <Op Opcode, typename P, size_t A>
struct GraphOp
{
    using Parameters = P;
    static constexpr size_t ARITY = A;
    static constexpr Op OPCODE = Opcode;
    Parameters params;
    std::array<size_t, ARITY> input_ids;
    virtual Result<void> evaluate_impl(
        Tensor &output, InputValues<ARITY> const &input_values) const = 0;

    virtual Result<TensorType>
    check_impl(InputTypes<ARITY> const &input_types) const = 0;

    Result<void>
    evaluate(Tensor &output, std::vector<Tensor> const &node_values) const
    {
        InputValues<ARITY> input_values{};
        for (size_t i = 0; i < ARITY; i++) {
            auto const input_id = input_ids[i];
            if (input_id >= node_values.size()) {
                return GraphEvalError::GraphValidationError;
            }
            input_values[i] = &node_values[input_id];
        }
        return evaluate_impl(output, input_values);
    }

    Result<TensorType> check(std::vector<TensorType> const &node_types) const
    {
        InputTypes<ARITY> input_types{};
        for (size_t i = 0; i < ARITY; i++) {
            auto const input_id = input_ids[i];
            if (input_id >= node_types.size()) {
                return GraphEvalError::GraphValidationError;
            }
            input_types[i] = &node_types[input_id];
        }
        return check_impl(input_types);
    }

protected:
    ~GraphOp() = default;
};

template <typename T>
concept IsGraphOp =
    std::derived_from<T, GraphOp<T::OPCODE, typename T::Parameters, T::ARITY>>;

template <typename OpT>
    requires(IsGraphOp<OpT>)
Result<OpT> read_next(std::span<uint8_t const> &graphcode)
{
    OpT op{};
    BOOST_OUTCOME_TRY(
        op.params, read_next<typename OpT::Parameters>(graphcode));
    for (size_t i = 0; i < OpT::ARITY; i++) {
        BOOST_OUTCOME_TRY(auto const input_id, read_next<uint16_t>(graphcode));
        op.input_ids[i] = input_id;
    }
    return op;
}

// Literal: a constant tensor, copied out of the graphcode
struct LiteralOp final
    : GraphOp<Op::Literal, std::tuple<TensorType, std::span<uint8_t const>>, 0>
{
    Result<TensorType> check_impl(InputTypes<0> const &) const override
    {
        auto const &[type, bytes] = params;
        if (type.size_bytes() != bytes.size_bytes()) {
            return GraphEvalError::GraphValidationError;
        }
        return type;
    }

    Result<void>
    evaluate_impl(Tensor &output, InputValues<0> const &) const override
    {
        auto const &[type, data] = params;
        // TODO: skip the copy by making the node's tensor a view of these
        // bytes, with no arena memory, as a Reshape shares its input's. Ops
        // read elements through T *, so the data must then be aligned: at an
        // aligned offset in the graphcode format, in a copy of the code that
        // Intercode allocates aligned
        std::memcpy(output.data(), data.data(), data.size());
        return outcome::success();
    }
};

struct TensorRefOp final
    : GraphOp<Op::TensorRef, std::tuple<TensorType, Address, uint32_t>, 0>
{
    Result<TensorType> check_impl(InputTypes<0> const &) const override
    {
        auto const &[type, address, offset] = params;
        return type;
    }

    Result<void> evaluate_impl(Tensor &, InputValues<0> const &) const override
    {
        // TODO: change this when we separate out `evaluate`
        MONAD_ABORT();
    }
};

// TODO: abstract over run_opN with template metaprogramming. run_op1 and
// run_op2 apply `f`, F{} by default, so that an F with parameters can be given
template <typename F, typename T, typename Out>
[[gnu::always_inline]]
inline void run_op1(
    T const *__restrict const xs, Out *__restrict const outs,
    uint64_t const length, bool const x_stride, F const f = F{})
{
    if (x_stride) {
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(f(xs[i]));
        }
    }
    else {
        auto const out = static_cast<Out>(f(xs[0]));
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
    bool const y_stride, F const f = F{})
{
    if (x_stride && y_stride) {
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(f(xs[i], ys[i]));
        }
    }
    else if (x_stride) {
        YT const y = ys[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(f(xs[i], y));
        }
    }
    else if (y_stride) {
        XT const x = xs[0];
        for (uint64_t i = 0; i < length; i++) {
            outs[i] = static_cast<Out>(f(x, ys[i]));
        }
    }
    else {
        auto const out = static_cast<Out>(f(xs[0], ys[0]));
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
template <Op Opcode, typename F>
struct ElementwiseOp2 final : GraphOp<Opcode, std::monostate, 2>
{
    // The output's element type for inputs of T
    template <typename T>
    using Out = std::conditional_t<
        std::same_as<std::invoke_result_t<F, T, T>, bool>, uint8_t,
        std::invoke_result_t<F, T, T>>;

    Result<TensorType>
    check_impl(InputTypes<2> const &input_types) const override
    {
        TensorType const &x = *input_types[0];
        TensorType const &y = *input_types[1];
        if (x.dtype() != y.dtype()) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const shape, broadcast_shape(std::array{x.shape(), y.shape()}));
        Dtype const dtype = visit_dtype(
            x.dtype(), []<typename T>() { return dtype_of<Out<T>>(); });
        return TensorType::checked(dtype, shape);
    }

    Result<void>
    evaluate_impl(Tensor &output, InputValues<2> const &inputs) const override
    {
        Tensor const &x = *inputs[0];
        Tensor const &y = *inputs[1];
        BOOST_OUTCOME_TRY(
            auto const loops, broadcast<2>({x.type().shape(), y.type().shape()}));

        return visit_dtype(x.type().dtype(), [&]<typename T>() -> Result<void> {
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

using AddOp = ElementwiseOp2<Op::Add, WrappingAdd>;
using SubOp = ElementwiseOp2<Op::Sub, WrappingSub>;

using GreaterOp = ElementwiseOp2<Op::Greater, std::greater<>>;

using GeOp = ElementwiseOp2<Op::Ge, std::greater_equal<>>;
using EqualOp = ElementwiseOp2<Op::Equal, std::equal_to<>>;
using MulOp = ElementwiseOp2<Op::Mul, WideningMul>;

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

using MaxOp = ElementwiseOp2<Op::Max, Maximum>;
using MinOp = ElementwiseOp2<Op::Min, Minimum>;

// Reshape: the input's elements under a new shape with the same element count.
// The result shares the input's data, which is safe while tensors are never
// written after they're produced
struct ReshapeOp final : GraphOp<Op::Reshape, Shape, 1>
{
    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        auto const &shape = params;
        TensorType const &x = *input_types[0];
        if (shape.size() != x.shape().size()) {
            return GraphEvalError::ShapeError;
        }
        return TensorType::checked(x.dtype(), shape);
    }

    Result<void> evaluate_impl(Tensor &, InputValues<1> const &) const override
    {
        return outcome::success();
    }
};

// Where: each element from x where the condition is nonzero, else from y, with
// the three shapes broadcast together. The condition is uint8, as comparisons
// return.
struct WhereOp final : GraphOp<Op::Where, std::monostate, 3>
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
    check_impl(InputTypes<3> const &input_types) const override
    {
        TensorType const &condition = *input_types[0];
        TensorType const &x = *input_types[1];
        TensorType const &y = *input_types[2];
        if (condition.dtype() != Dtype::uint8 || x.dtype() != y.dtype()) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const shape,
            broadcast_shape(std::array{condition.shape(), x.shape(), y.shape()}));
        return TensorType::checked(x.dtype(), shape);
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<3> const &inputs) const override
    {
        Tensor const &condition = *inputs[0];
        Tensor const &x = *inputs[1];
        Tensor const &y = *inputs[2];
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<3>(
                {condition.type().shape(), x.type().shape(), y.type().shape()}));

        visit_dtype(x.type().dtype(), [&]<typename T>() {
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
struct SaturateOp final : GraphOp<Op::Saturate, Dtype, 1>
{
    template <typename To>
    struct Impl
    {
        template <typename From>
        To operator()(From const x) const
        {
            if (std::cmp_less(x, std::numeric_limits<To>::min())) {
                return std::numeric_limits<To>::min();
            }
            if (std::cmp_greater(x, std::numeric_limits<To>::max())) {
                return std::numeric_limits<To>::max();
            }
            return static_cast<To>(x); // NOLINT(bugprone-signed-char-misuse)
        }
    };

    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        auto const dtype = params;
        return TensorType::checked(dtype, input_types[0]->shape());
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<1> const &inputs) const override
    {
        auto const dtype = params;
        Tensor const &x = *inputs[0];
        visit_dtype(x.type().dtype(), [&]<typename From>() {
            visit_dtype(dtype, [&]<typename To>() {
                // The output has the input's shape, so it's all one run.
                // Going through run_op1's restrict pointers lets GCC
                // vectorize the conversions whose types may alias, such as
                // any to or from int8 or uint8, without a runtime alias check
                auto const xs = x.elements<From const>();
                auto const outs = out.elements<To>();
                run_op1<Impl<To>>(xs.data(), outs.data(), outs.size(), true);
            });
        });
        return outcome::success();
    }
};

// TODO: we don't need/want CAST at all
struct CastOp final : GraphOp<Op::Cast, Dtype, 1>
{
    Result<TensorType> check_impl(InputTypes<1> const &) const override
    {
        // TODO
        MONAD_ABORT();
    }

    Result<void> evaluate_impl(Tensor &, InputValues<1> const &) const override
    {
        MONAD_ABORT();
    }
};

// Expand: broadcasts the input to the shape given as its parameter, as
// numpy.broadcast_to does. The input's dimensions are matched against the
// shape's last ones, and each must equal its counterpart or be 1, in which case
// the input is repeated along it. Element-wise ops broadcast their operands
// themselves, so this is only needed for a broadcast tensor on its own.
struct ExpandOp final : GraphOp<Op::Expand, Shape, 1>
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
    check_impl(InputTypes<1> const &input_types) const override
    {
        auto const &shape = params;
        TensorType const &x = *input_types[0];
        if (x.shape().rank() > shape.rank()) {
            return GraphEvalError::RankError;
        }
        BOOST_OUTCOME_TRY(
            auto const broadcast, broadcast_shape(std::array{shape, x.shape()}));
        if (broadcast != shape) {
            return GraphEvalError::ShapeError;
        }
        return TensorType::checked(x.dtype(), shape);
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<1> const &inputs) const override
    {
        auto const &shape = params;
        Tensor const &x = *inputs[0];
        // Broadcasting the input against the shape gives back the shape
        // exactly when each of the input's dimensions matches it or is 1
        BOOST_OUTCOME_TRY(
            auto const loops, broadcast<2>({shape, x.type().shape()}));

        visit_dtype(x.type().dtype(), [&]<typename T>() {
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
struct DivOp final : GraphOp<Op::Div, int64_t, 1>
{

    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        auto const denominator = params;
        if (denominator == 0) {
            return GraphEvalError::GraphValidationError;
        }
        return *input_types[0];
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<1> const &inputs) const override
    {
        auto const denominator = params;
        Tensor const &x = *inputs[0];
        visit_dtype(x.type().dtype(), [&]<typename T>() {
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
struct MatMulOp final : GraphOp<Op::MatMul, std::monostate, 2>
{

    Result<TensorType>
    check_impl(InputTypes<2> const &input_types) const override
    {
        TensorType const &x = *input_types[0];
        TensorType const &y = *input_types[1];
        if (x.dtype() != Dtype::int8 || y.dtype() != Dtype::int8) {
            return GraphEvalError::TypeError;
        }
        if (x.shape().rank() != 2 || y.shape().rank() != 2) {
            return GraphEvalError::RankError;
        }
        if (y.shape().dimensions()[0] != x.shape().dimensions()[1]) {
            return GraphEvalError::ShapeError;
        }
        BOOST_OUTCOME_TRY(
            auto const shape,
            Shape::checked(2, {x.shape().dimensions()[0], y.shape().dimensions()[1]}));
        return TensorType::checked(Dtype::int32, shape);
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<2> const &inputs) const override
    {
        Tensor const &x = *inputs[0];
        Tensor const &y = *inputs[1];
        matmul_i8(x, y, out);
        return outcome::success();
    }
};

// ArgMax: the row-major index of the input's largest element, the first of any
// equal ones, as a scalar of the input's dtype, so an index that doesn't fit
// wraps. An empty input has none.
struct ArgMaxOp final : GraphOp<Op::ArgMax, std::monostate, 1>
{

    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        TensorType const &x = *input_types[0];
        if (x.shape().size() == 0) {
            return GraphEvalError::ShapeError;
        }
        return TensorType::checked(x.dtype(), Shape{});
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<1> const &inputs) const override
    {
        Tensor const &x = *inputs[0];
        visit_dtype(x.type().dtype(), [&]<typename T>() {
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

struct ArgMinOp final : GraphOp<Op::ArgMin, std::monostate, 1>
{

    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        TensorType const &x = *input_types[0];
        if (x.shape().size() == 0) {
            return GraphEvalError::ShapeError;
        }
        return TensorType::checked(x.dtype(), Shape{});
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<1> const &inputs) const override
    {
        Tensor const &x = *inputs[0];
        visit_dtype(x.type().dtype(), [&]<typename T>() {
            auto const xs = x.elements<T const>();
            size_t smallest = 0;
            for (size_t i = 1; i < xs.size(); i++) {
                if (xs[smallest] > xs[i]) {
                    smallest = i;
                }
            }
            out.elements<T>()[0] = static_cast<T>(smallest);
        });
        return outcome::success();
    }
};

struct ClipOp final
    : GraphOp<Op::Clip, std::tuple<Dtype, uint64_t, uint64_t>, 1>
{
    Result<TensorType> check_impl(InputTypes<1> const &) const override
    {
        // TODO
        MONAD_ABORT();
    }

    Result<void> evaluate_impl(Tensor &, InputValues<1> const &) const override
    { // TODO
        MONAD_ABORT();
    }
};

// CumSum: running sums along the axis given as its parameter, inclusive and in
// increasing index order, wrapping on overflow like Add
struct CumSumOp final : GraphOp<Op::CumSum, uint8_t, 1>
{
    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        auto const axis = params;
        TensorType const &x = *input_types[0];
        if (axis >= x.shape().rank()) {
            return GraphEvalError::RankError;
        }
        return x;
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<1> const &inputs) const override
    {
        auto const axis = params;
        Tensor const &x = *inputs[0];

        // The input as `outer` blocks of `length` rows of `inner` elements,
        // with the axis running down the rows
        uint64_t outer = 1;
        for (size_t i = 0; i < axis; i++) {
            outer *= x.type().shape().dimensions()[i];
        }
        uint64_t const length = x.type().shape().dimensions()[axis];
        uint64_t inner = 1;
        for (size_t i = axis + 1u; i < x.type().shape().rank(); i++) {
            inner *= x.type().shape().dimensions()[i];
        }

        visit_dtype(x.type().dtype(), [&]<typename T>() {
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

// Applies F element by element to two tensors of the same dtype, read as
// fixed-point numbers with the number of fractional bits given as the op's
// parameter, with their shapes broadcast together. The output has their dtype
// and the broadcast shape. F::check checks the inputs' elements first
template <Op Opcode, typename F>
struct FixedPointOp2 final : GraphOp<Opcode, uint8_t, 2>
{
    using GraphOp<Opcode, uint8_t, 2>::params;

    Result<TensorType>
    check_impl(InputTypes<2> const &input_types) const override
    {
        auto const bits = params;
        TensorType const &x = *input_types[0];
        TensorType const &y = *input_types[1];
        // TODO: also bound bits by the dtype's width, here and in
        // evaluate_impl. As it is, a uint8 can have 35 fractional bits, which
        // leaves it only values below 2^-27
        if (bits > MAX_FRACTIONAL_BITS) {
            return GraphEvalError::GraphValidationError;
        }
        if (x.dtype() != y.dtype()) {
            return GraphEvalError::TypeError;
        }
        BOOST_OUTCOME_TRY(
            auto const shape, broadcast_shape(std::array{x.shape(), y.shape()}));
        return TensorType::checked(x.dtype(), shape);
    }

    Result<void>
    evaluate_impl(Tensor &output, InputValues<2> const &inputs) const override
    {
        auto const bits = params;
        Tensor const &x = *inputs[0];
        Tensor const &y = *inputs[1];
        BOOST_OUTCOME_TRY(
            auto const loops, broadcast<2>({x.type().shape(), y.type().shape()}));

        return visit_dtype(x.type().dtype(), [&]<typename T>() -> Result<void> {
            BOOST_OUTCOME_TRY(
                F::check(x.elements<T const>(), y.elements<T const>()));
            T const *const xs = x.elements<T const>().data();
            T const *const ys = y.elements<T const>().data();
            T *const outs = output.elements<T>().data();
            F const f{bits};
            for_each_run(
                loops,
                [&](auto const &offsets,
                    uint64_t start,
                    uint64_t length,
                    auto const &strides) {
                    run_op2(
                        xs + offsets[0],
                        ys + offsets[1],
                        outs + start,
                        length,
                        strides[0],
                        strides[1],
                        f);
                });
            return outcome::success();
        });
    }
};

// Fixed-point multiplication: floor(x * y / 2^bits), wrapping on overflow
struct FixedPointMul
{
    unsigned bits;

    template <typename T>
    static Result<void> check(std::span<T const>, std::span<T const>)
    {
        return outcome::success();
    }

    template <typename T>
    T operator()(T const x, T const y) const
    {
        return q_mul(x, y, bits);
    }
};

// Fixed-point division: x * 2^bits / y, truncated toward zero and wrapping on
// overflow. DivisionByZero if any of y's elements is zero
struct FixedPointDiv
{
    unsigned bits;

    template <typename T>
    static Result<void> check(std::span<T const>, std::span<T const> const ys)
    {
        for (T const y : ys) {
            if (y == 0) {
                return GraphEvalError::DivisionByZero;
            }
        }
        return outcome::success();
    }

    template <typename T>
    T operator()(T const x, T const y) const
    {
        return q_div(x, y, bits);
    }
};

using QMulOp = FixedPointOp2<Op::QMul, FixedPointMul>;
using QDivOp = FixedPointOp2<Op::QDiv, FixedPointDiv>;

// QMatMul: the fixed-point product of two matrices of the same dtype, with the
// number of fractional bits and the output's dtype as its parameters. Each
// element's products are summed exactly, wrapping at 128 bits, then shifted
// right by the number of fractional bits, rounding down, and wrapped to the
// output's dtype. For int8 matrices, 0 bits and int32 out, it's MatMul
struct QMatMulOp final : GraphOp<Op::QMatMul, std::tuple<uint8_t, Dtype>, 2>
{
    Result<TensorType>
    check_impl(InputTypes<2> const &input_types) const override
    {
        auto const &[bits, out_dtype] = params;
        TensorType const &x = *input_types[0];
        TensorType const &y = *input_types[1];
        // TODO: also bound bits by the inputs' dtype width, here and in
        // evaluate_impl, as for the other fixed-point ops
        if (bits > MAX_FRACTIONAL_BITS) {
            return GraphEvalError::GraphValidationError;
        }
        if (x.dtype() != y.dtype()) {
            return GraphEvalError::TypeError;
        }
        if (x.shape().rank() != 2 || y.shape().rank() != 2) {
            return GraphEvalError::RankError;
        }
        if (y.shape().dimensions()[0] != x.shape().dimensions()[1]) {
            return GraphEvalError::ShapeError;
        }
        BOOST_OUTCOME_TRY(auto const shape, Shape::checked(2, {x.shape().dimensions()[0], y.shape().dimensions()[1]}));
        return TensorType::checked(
            out_dtype,
            shape);
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<2> const &inputs) const override
    {
        auto const &[bits, out_dtype] = params;
        Tensor const &x = *inputs[0];
        Tensor const &y = *inputs[1];

        matmul(x, y, bits, out);
        return outcome::success();
    }
};

// Reduce: combines the input's elements along the axis given as its parameter
// with F. The result keeps the axis, with length 1, so that it broadcasts
// against the input. An empty axis reduces to 0 if `empty_is_zero`, and is a
// ShapeError otherwise
template <Op Opcode, typename F, bool empty_is_zero>
struct ReduceOp final : GraphOp<Opcode, uint8_t, 1>
{
    using GraphOp<Opcode, uint8_t, 1>::params;

    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        auto const axis = params;
        TensorType const &x = *input_types[0];
        if (axis >= x.shape().rank()) {
            return GraphEvalError::RankError;
        }
        if (!empty_is_zero && x.shape().dimensions()[axis] == 0) {
            return GraphEvalError::ShapeError;
        }
        auto const rank = x.shape().rank();
        auto dimensions = x.shape().dimensions();
        dimensions[axis] = 1;
        BOOST_OUTCOME_TRY(auto const shape, Shape::checked(rank, dimensions));
        return TensorType::checked(x.dtype(), shape);
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<1> const &inputs) const override
    {
        auto const axis = params;
        Tensor const &x = *inputs[0];
        uint64_t const length = x.type().shape().dimensions()[axis];

        // The input as `outer` blocks of `length` rows of `inner` elements,
        // with the axis running down the rows, as in CumSum. Each block
        // reduces to one row of the output
        uint64_t outer = 1;
        for (size_t i = 0; i < axis; i++) {
            outer *= x.type().shape().dimensions()[i];
        }
        uint64_t inner = 1;
        for (size_t i = axis + 1u; i < x.type().shape().rank(); i++) {
            inner *= x.type().shape().dimensions()[i];
        }

        visit_dtype(x.type().dtype(), [&]<typename T>() {
            T const *const xs = x.elements<T const>().data();
            T *const outs = out.elements<T>().data();
            for (uint64_t block = 0; block < outer; block++) {
                T const *__restrict const rows = xs + block * length * inner;
                T *__restrict const result = outs + block * inner;
                if (length == 0) {
                    std::fill_n(result, inner, T{0});
                    continue;
                }
                std::copy_n(rows, inner, result);
                for (uint64_t row = 1; row < length; row++) {
                    for (uint64_t i = 0; i < inner; i++) {
                        result[i] = F{}(result[i], rows[row * inner + i]);
                    }
                }
            }
        });
        return outcome::success();
    }
};

using ReduceSumOp = ReduceOp<Op::ReduceSum, WrappingAdd, true>;
using ReduceMaxOp = ReduceOp<Op::ReduceMax, Maximum, false>;

// Applies F element by element to a tensor, read as fixed-point numbers with
// the number of fractional bits given as the op's parameter, into a tensor of
// its dtype and shape. F::check checks the input's elements first
template <Op Opcode, typename F>
struct FixedPointOp1 final : GraphOp<Opcode, uint8_t, 1>
{
    using GraphOp<Opcode, uint8_t, 1>::params;

    Result<TensorType>
    check_impl(InputTypes<1> const &input_types) const override
    {
        auto const bits = params;
        // TODO: also bound bits by the dtype's width, here and in
        // evaluate_impl. As it is, a uint8 can have 35 fractional bits, which
        // leaves it only values below 2^-27
        if (bits > MAX_FRACTIONAL_BITS) {
            return GraphEvalError::GraphValidationError;
        }
        return *input_types[0];
    }

    Result<void>
    evaluate_impl(Tensor &output, InputValues<1> const &inputs) const override
    {
        auto const bits = params;
        Tensor const &x = *inputs[0];
        return visit_dtype(x.type().dtype(), [&]<typename T>() -> Result<void> {
            auto const xs = x.elements<T const>();
            BOOST_OUTCOME_TRY(F::check(xs));
            auto const outs = output.elements<T>();
            run_op1(xs.data(), outs.data(), outs.size(), true, F{bits});
            return outcome::success();
        });
    }
};

// Fixed-point e^x, rounded down and saturating, as q_exp computes it
struct FixedPointExp
{
    unsigned bits;

    template <typename T>
    static Result<void> check(std::span<T const>)
    {
        return outcome::success();
    }

    template <typename T>
    T operator()(T const x) const
    {
        return q_exp(x, bits);
    }
};

// Fixed-point 1 / sqrt(x), rounded down and saturating. Of the elements, in
// row-major order, the first that isn't positive fails: with DivisionByZero if
// it's zero, and DomainError if it's negative
struct FixedPointInvSqrt
{
    unsigned bits;

    template <typename T>
    static Result<void> check(std::span<T const> const xs)
    {
        for (T const x : xs) {
            if (x == 0) {
                return GraphEvalError::DivisionByZero;
            }
            if (std::cmp_less(x, 0)) {
                return GraphEvalError::DomainError;
            }
        }
        return outcome::success();
    }

    template <typename T>
    T operator()(T const x) const
    {
        return q_inv_sqrt(x, bits);
    }
};

using QExpOp = FixedPointOp1<Op::QExp, FixedPointExp>;
using QInvSqrtOp = FixedPointOp1<Op::QInvSqrt, FixedPointInvSqrt>;

// The product of a shape's dimensions in [begin, end), and of `size`
inline uint64_t dimensions_product(
    Shape const &shape, size_t const begin, size_t const end,
    uint64_t const size = 1)
{
    uint64_t product = size;
    for (size_t i = begin; i < end; i++) {
        product *= shape.dimensions()[i];
    }
    return product;
}

// Gather: the slices of `data` along the axis given as its parameter at each
// of `indices`, which can have any dtype, as in numpy.take and ONNX. The
// result's dimensions are data's before the axis, then the indices', then
// data's after the axis. IndexError if an index isn't in [0, n), for data's
// length n along the axis
struct GatherOp final : GraphOp<Op::Gather, uint8_t, 2>
{
    Result<TensorType>
    check_impl(InputTypes<2> const &input_types) const override
    {
        auto const axis = params;
        TensorType const &input = *input_types[0];
        Shape const &indices = input_types[1]->shape();
        if (axis >= input.shape().rank()) {
            return GraphEvalError::RankError;
        }
        size_t const output_rank = input.shape().rank() - 1u + indices.rank();
        if (output_rank > input.shape().dimensions().size()) {
            return GraphEvalError::RankError;
        }
        auto const rank = static_cast<uint8_t>(output_rank);
        std::array<uint16_t, MAX_RANK> dimensions{};
        auto const *const input_dimensions = input.shape().dimensions().begin();
        auto *out = std::copy_n(input_dimensions, axis, dimensions.begin());
        out = std::copy_n(indices.dimensions().begin(), indices.rank(), out);
        std::copy(
            input_dimensions + axis + 1,
            input_dimensions + input.shape().rank(),
            out);

        BOOST_OUTCOME_TRY(auto const shape, Shape::checked(rank, dimensions));
        return TensorType::checked(input.dtype(), shape);
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<2> const &inputs) const override
    {
        auto const axis = params;
        Tensor const &data = *inputs[0];
        Tensor const &indices = *inputs[1];
        Shape const &shape = data.type().shape();

        // Data as `outer` blocks of `length` slices of `slice` bytes. Each
        // block gives the result a slice per index
        uint64_t const length = shape.dimensions()[axis];
        uint64_t const outer = dimensions_product(shape, 0, axis);
        uint64_t const slice = dimensions_product(
            shape, axis + 1u, shape.rank(), dtype_size(data.type().dtype()));

        return visit_dtype(
            indices.type().dtype(), [&]<typename I>() -> Result<void> {
                auto const ids = indices.elements<I const>();
                for (I const id : ids) {
                    if (std::cmp_less(id, 0) ||
                        std::cmp_greater_equal(id, length)) {
                        return GraphEvalError::IndexError;
                    }
                }
                uint8_t *to = out.data();
                for (uint64_t block = 0; block < outer; block++) {
                    uint8_t const *const slices =
                        data.data() + block * length * slice;
                    for (I const id : ids) {
                        std::memcpy(
                            to,
                            slices + static_cast<uint64_t>(id) * slice,
                            slice);
                        to += slice;
                    }
                }
                return outcome::success();
            });
    }
};

// Concat: a and b joined along the axis given as its parameter, a's slices
// first. They must have the same dtype and rank, and the same dimensions but
// along the axis, where the result's is the sum, which must fit a dimension
struct ConcatOp final : GraphOp<Op::Concat, uint8_t, 2>
{
    static Result<TensorType>
    type(uint8_t const axis, TensorType const &a, TensorType const &b)
    {
        if (a.dtype() != b.dtype()) {
            return GraphEvalError::TypeError;
        }
        if (a.shape().rank() != b.shape().rank() || axis >= a.shape().rank()) {
            return GraphEvalError::RankError;
        }
        for (size_t i = 0; i < a.shape().rank(); i++) {
            if (i != axis && a.shape().dimensions()[i] != b.shape().dimensions()[i]) {
                return GraphEvalError::ShapeError;
            }
        }
        uint32_t const length =
            uint32_t{a.shape().dimensions()[axis]} + b.shape().dimensions()[axis];
        if (length > std::numeric_limits<uint16_t>::max()) {
            return GraphEvalError::ShapeError;
        }
        auto const rank = a.shape().rank();
        std::array<uint16_t, MAX_RANK> dimensions = a.shape().dimensions();
        dimensions[axis] = static_cast<uint16_t>(length);
        BOOST_OUTCOME_TRY(auto const shape, Shape::checked(rank, dimensions));
        return TensorType::checked(a.dtype(), shape);
    }

    Result<TensorType>
    check_impl(InputTypes<2> const &input_types) const override
    {
        auto const axis = params;
        return type(axis, *input_types[0], *input_types[1]);
    }

    Result<void>
    evaluate_impl(Tensor &out, InputValues<2> const &inputs) const override
    {
        auto const axis = params;
        Tensor const &a = *inputs[0];
        Tensor const &b = *inputs[1];
        BOOST_OUTCOME_TRY(type(axis, a.type(), b.type()));

        // Each as `outer` blocks, which alternate in the result, a's first
        Shape const &shape = a.type().shape();
        uint64_t const outer = dimensions_product(shape, 0, axis);
        uint64_t const inner = dimensions_product(
            shape, axis + 1u, shape.rank(), dtype_size(a.type().dtype()));
        uint64_t const a_block = shape.dimensions()[axis] * inner;
        uint64_t const b_block = b.type().shape().dimensions()[axis] * inner;
        uint8_t *to = out.data();
        for (uint64_t block = 0; block < outer; block++) {
            std::memcpy(to, a.data() + block * a_block, a_block);
            to += a_block;
            std::memcpy(to, b.data() + block * b_block, b_block);
            to += b_block;
        }
        return outcome::success();
    }
};

namespace detail
{
    template <typename... Fs>
    struct Overloaded : Fs...
    {
        using Fs::operator()...;
    };

    template <typename... Fs>
    using VisitResult = std::invoke_result_t<
        Overloaded<std::decay_t<Fs>...> const &, LiteralOp const &>;
}

template <typename... Fs>
[[gnu::always_inline]]
inline detail::VisitResult<Fs...>
visit_next(std::span<uint8_t const> &graphcode, Fs &&...fs)
{
    detail::Overloaded<std::decay_t<Fs>...> const visitor{
        std::forward<Fs>(fs)...};
    auto const visit = [&]<typename OpT>() -> detail::VisitResult<Fs...> {
        BOOST_OUTCOME_TRY(auto const op, read_next<OpT>(graphcode));
        return visitor(op);
    };

    BOOST_OUTCOME_TRY(auto const opcode, read_next<Op>(graphcode));
    switch (opcode) {
    case LiteralOp::OPCODE:
        return visit.template operator()<LiteralOp>();
    case TensorRefOp::OPCODE:
        return visit.template operator()<TensorRefOp>();
    case AddOp::OPCODE:
        return visit.template operator()<AddOp>();
    case SubOp::OPCODE:
        return visit.template operator()<SubOp>();
    case GreaterOp::OPCODE:
        return visit.template operator()<GreaterOp>();
    case GeOp::OPCODE:
        return visit.template operator()<GeOp>();
    case EqualOp::OPCODE:
        return visit.template operator()<EqualOp>();
    case ReshapeOp::OPCODE:
        return visit.template operator()<ReshapeOp>();
    case WhereOp::OPCODE:
        return visit.template operator()<WhereOp>();
    case CumSumOp::OPCODE:
        return visit.template operator()<CumSumOp>();
    case SaturateOp::OPCODE:
        return visit.template operator()<SaturateOp>();
    case MatMulOp::OPCODE:
        return visit.template operator()<MatMulOp>();
    case ArgMaxOp::OPCODE:
        return visit.template operator()<ArgMaxOp>();
    case ArgMinOp::OPCODE:
        return visit.template operator()<ArgMinOp>();
    case ClipOp::OPCODE:
        return visit.template operator()<ClipOp>();
    case MaxOp::OPCODE:
        return visit.template operator()<MaxOp>();
    case MinOp::OPCODE:
        return visit.template operator()<MinOp>();
    case MulOp::OPCODE:
        return visit.template operator()<MulOp>();
    case DivOp::OPCODE:
        return visit.template operator()<DivOp>();
    case CastOp::OPCODE:
        return visit.template operator()<CastOp>();
    case ExpandOp::OPCODE:
        return visit.template operator()<ExpandOp>();
    case QMulOp::OPCODE:
        return visit.template operator()<QMulOp>();
    case QDivOp::OPCODE:
        return visit.template operator()<QDivOp>();
    case QMatMulOp::OPCODE:
        return visit.template operator()<QMatMulOp>();
    case ReduceSumOp::OPCODE:
        return visit.template operator()<ReduceSumOp>();
    case ReduceMaxOp::OPCODE:
        return visit.template operator()<ReduceMaxOp>();
    case QExpOp::OPCODE:
        return visit.template operator()<QExpOp>();
    case QInvSqrtOp::OPCODE:
        return visit.template operator()<QInvSqrtOp>();
    case GatherOp::OPCODE:
        return visit.template operator()<GatherOp>();
    case ConcatOp::OPCODE:
        return visit.template operator()<ConcatOp>();
    }
    MONAD_ABORT();
}

MONAD_GRAPH_EVAL_NAMESPACE_END
