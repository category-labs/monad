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

#include <category/core/assert.h>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <boost/outcome/try.hpp>

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <tuple>
#include <type_traits>
#include <utility>
#include <variant>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

enum class Op : uint16_t
{
    Literal = 0,
    TensorRef,
    Add,
    Sub,
    Greater,
    Ge,
    Equal,
    Reshape,
    Where,
    CumSum,
    Saturate,
    MatMul,
    ArgMax,
    ArgMin,
    Clip,
    Max,
    Min,
    Mul,
    Div,
    Cast,
    Expand,
    Last_valid_op = Expand,
};

inline char const *op_name(Op const op)
{
    switch (op) {
    case Op::Literal:
        return "Literal";
    case Op::TensorRef:
        return "TensorRef";
    case Op::Add:
        return "Add";
    case Op::Sub:
        return "Sub";
    case Op::Greater:
        return "Greater";
    case Op::Ge:
        return "Ge";
    case Op::Equal:
        return "Equal";
    case Op::Reshape:
        return "Reshape";
    case Op::Where:
        return "Where";
    case Op::CumSum:
        return "CumSum";
    case Op::Saturate:
        return "Saturate";
    case Op::MatMul:
        return "MatMul";
    case Op::ArgMax:
        return "ArgMax";
    case Op::ArgMin:
        return "ArgMin";
    case Op::Clip:
        return "Clip";
    case Op::Max:
        return "Max";
    case Op::Min:
        return "Min";
    case Op::Mul:
        return "Mul";
    case Op::Div:
        return "Div";
    case Op::Cast:
        return "Cast";
    case Op::Expand:
        return "Expand";
    }
    MONAD_ABORT();
}

//
// Reading graphcode. Each read_next<T> consumes a T from the front of its
// input, which is in host byte order.
//

template <typename T>
Result<T> read_next(std::span<uint8_t const> &);

template <typename T>
    requires(std::integral<T>)
[[gnu::always_inline]]
inline Result<T> read_next(std::span<uint8_t const> &input)
{
    if (input.size() < sizeof(T)) {
        return GraphEvalError::GraphValidationError;
    }

    std::remove_cv_t<T> result{};
    std::memcpy(&result, input.data(), sizeof(result));
    input = input.subspan(sizeof(T));
    return result;
}

// Rejects bytes that don't name a Dtype, so the result is always safe to pass
// to dtype_size, which aborts on anything else
template <>
[[gnu::always_inline]]
inline Result<Dtype> read_next<Dtype>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const id, read_next<std::underlying_type_t<Dtype>>(input));
    if (id >
        static_cast<std::underlying_type_t<Dtype>>(Dtype::Last_valid_dtype)) {
        return GraphEvalError::TypeError;
    }
    return static_cast<Dtype>(id);
}

// Parameters of an op that takes none, encoded as zero bytes
template <>
[[gnu::always_inline]]
inline Result<std::monostate>
read_next<std::monostate>(std::span<uint8_t const> &)
{
    return std::monostate{};
}

// Rank (uint8), then `rank` dimensions (uint16 each). Rejects shapes whose
// element count overflows uint64, so Shape::size() is exact
template <>
[[gnu::always_inline]]
inline Result<Shape> read_next<Shape>(std::span<uint8_t const> &input)
{
    Shape shape{};
    BOOST_OUTCOME_TRY(shape.rank, read_next<uint8_t>(input));
    if (shape.rank > shape.dimensions.size()) {
        return GraphEvalError::RankError;
    }

    uint64_t size = 1;
    for (size_t i = 0; i < shape.rank; i++) {
        BOOST_OUTCOME_TRY(shape.dimensions[i], read_next<uint16_t>(input));
        if (MONAD_UNLIKELY(
                __builtin_mul_overflow(size, shape.dimensions[i], &size))) {
            return GraphEvalError::ShapeError;
        }
    }
    return shape;
}

template <typename T>
inline constexpr bool is_tuple_v = false;

template <typename... Ts>
inline constexpr bool is_tuple_v<std::tuple<Ts...>> = true;

// Reads the elements in order. Function templates can't be partially
// specialized, so tuples get an overload constrained to them instead
template <typename T>
    requires(is_tuple_v<T>)
[[gnu::always_inline]]
inline Result<T> read_next(std::span<uint8_t const> &input)
{
    if constexpr (std::tuple_size_v<T> == 0) {
        return T{};
    }
    else {
        return [&]<typename Head, typename... Tail>(
                   std::type_identity<std::tuple<Head, Tail...>>) -> Result<T> {
            BOOST_OUTCOME_TRY(auto head, read_next<Head>(input));
            BOOST_OUTCOME_TRY(auto tail, read_next<std::tuple<Tail...>>(input));
            return std::tuple_cat(
                std::tuple<Head>{std::move(head)}, std::move(tail));
        }(std::type_identity<T>{});
    }
}

// Consumes the next `size` bytes of `input`
Result<std::span<uint8_t const>>
read_bytes(std::span<uint8_t const> &input, uint64_t size);

// Literal parameters: a tensor header, then the data, packed row-major in the
// same byte order as the rest of the graphcode. The data's length depends on
// the header, so unlike other tuples this one isn't read element by element.
// Reading the data here, before the op allocates anything, means a literal
// can't claim more data than the graphcode holds and get that much memory
// allocated
template <>
[[gnu::always_inline]]
inline Result<std::tuple<TensorType, std::span<uint8_t const>>>
read_next<std::tuple<TensorType, std::span<uint8_t const>>>(
    std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const header, read_next<std::tuple<Dtype, Shape>>(input));
    auto const &[dtype, shape] = header;
    BOOST_OUTCOME_TRY(auto const size, tensor_size_bytes(dtype, shape));
    BOOST_OUTCOME_TRY(auto const data, read_bytes(input, size));
    return std::tuple{TensorType{dtype, shape}, data};
}

MONAD_GRAPH_EVAL_NAMESPACE_END
