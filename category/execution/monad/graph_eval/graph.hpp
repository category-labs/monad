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

#include "category/execution/monad/graph_eval/constants.hpp"
#include <category/core/address.hpp>
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

//
// Reading graphcode. Each read_next<T> consumes a T from the front of its
// input, which is in host byte order.
//
template <typename T>
    requires(std::is_trivially_copyable_v<T> || std::is_void_v<T>)
T read_next_unchecked(std::span<uint8_t const> &input)
{
    std::remove_cv_t<T> result{};
    std::memcpy(&result, input.data(), sizeof(result));
    input = input.subspan(sizeof(T));
    return result;
}

// Deleted, so that read_next reads only what it's defined for: the dtypes,
// tuples, ops, and the types it's specialized for, below and wherever those
// types are defined
template <typename T>
Result<T> read_next(std::span<uint8_t const> &) = delete;

template <dtype_t T>
[[gnu::always_inline]]
inline Result<T> read_next(std::span<uint8_t const> &input)
{
    if (input.size() < sizeof(T)) {
        return GraphEvalError::GraphValidationError;
    }
    return read_next_unchecked<T>(input);
}

template <>
[[gnu::always_inline]]
inline Result<Dtype> read_next<Dtype>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const ty_id, read_next<std::underlying_type_t<Dtype>>(input));
    if (ty_id >
        static_cast<std::underlying_type_t<Dtype>>(Dtype::Last_valid_dtype)) {
        return GraphEvalError::TypeError;
    }
    return static_cast<Dtype>(ty_id);
}

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
    BOOST_OUTCOME_TRY(auto const rank, read_next<uint8_t>(input));
    if (rank > MAX_RANK) {
        return GraphEvalError::RankError;
    }

    std::array<uint16_t, MAX_RANK> dimensions;
    for (size_t i = 0; i < rank; i++) {
        BOOST_OUTCOME_TRY(dimensions[i], read_next<uint16_t>(input));
    }

    return Shape::checked(rank, dimensions);
}

template <>
[[gnu::always_inline]]
inline Result<TensorType> read_next<TensorType>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(auto const dtype, read_next<Dtype>(input));
    BOOST_OUTCOME_TRY(auto const shape, read_next<Shape>(input));
    return TensorType::checked(dtype, shape);
}

template <>
[[gnu::always_inline]]
inline Result<Address> read_next<Address>(std::span<uint8_t const> &input)
{
    Address address;
    if (input.size() < sizeof(address.bytes)) {
        return GraphEvalError::GraphValidationError;
    }
    std::memcpy(address.bytes, input.data(), sizeof(address.bytes));
    input = input.subspan(sizeof(address.bytes));
    return address;
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

[[gnu::always_inline]]
inline std::span<uint8_t const>
read_bytes_unchecked(std::span<uint8_t const> &input, uint64_t const size)
{
    auto const bytes = input.first(static_cast<size_t>(size));
    input = input.subspan(static_cast<size_t>(size));
    return bytes;
}

[[gnu::always_inline]]
inline Result<std::span<uint8_t const>>
read_bytes(std::span<uint8_t const> &input, uint64_t const size)
{
    if (input.size() < size) {
        return GraphEvalError::GraphValidationError;
    }
    return read_bytes_unchecked(input, size);
}

template <>
[[gnu::always_inline]]
inline Result<std::tuple<TensorType, std::span<uint8_t const>>>
read_next<std::tuple<TensorType, std::span<uint8_t const>>>(
    std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(auto const type, read_next<TensorType>(input));
    BOOST_OUTCOME_TRY(auto const data, read_bytes(input, type.size_bytes()));
    return std::tuple{type, data};
}

template <auto expected>
[[gnu::always_inline]]
inline Result<void> expect_next(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        decltype(expected) const item, read_next<decltype(expected)>(input));
    if (item != expected) {
        return GraphEvalError::GraphValidationError;
    }
    return outcome::success();
}

template <typename T>
[[gnu::always_inline]] inline T take(uint8_t const *&code) = delete;

template <dtype_t T>
[[gnu::always_inline]] inline T take(uint8_t const *&code)
{
    std::remove_cv_t<T> result{};
    std::memcpy(&result, code, sizeof(result));
    code += sizeof(T);
    return result;
}

template <>
[[gnu::always_inline]] inline Dtype take<Dtype>(uint8_t const *&code)
{
    return static_cast<Dtype>(take<std::underlying_type_t<Dtype>>(code));
}

template <>
[[gnu::always_inline]] inline Shape take<Shape>(uint8_t const *&code)
{
    auto const rank = take<uint8_t>(code);
    std::array<uint16_t, MAX_RANK> dimensions{};
    for (size_t i = 0; i < rank; i++) {
        dimensions[i] = take<uint16_t>(code);
    }
    return Shape::checked(rank, dimensions).assume_value();
}

template <>
[[gnu::always_inline]] inline TensorType take<TensorType>(uint8_t const *&code)
{
    auto const dtype = take<Dtype>(code);
    auto const shape = take<Shape>(code);
    return TensorType::checked(dtype, shape).assume_value();
}

template <>
[[gnu::always_inline]] inline Address take<Address>(uint8_t const *&code)
{
    Address address;
    std::memcpy(address.bytes, code, sizeof(address.bytes));
    code += sizeof(address.bytes);
    return address;
}

template <typename T>
[[gnu::always_inline]] inline void skip(uint8_t const *&code) = delete;

template <dtype_t T>
[[gnu::always_inline]] inline void skip(uint8_t const *&code)
{
    code += sizeof(T);
}

template <>
[[gnu::always_inline]] inline void skip<Dtype>(uint8_t const *&code)
{
    skip<std::underlying_type_t<Dtype>>(code);
}

template <>
[[gnu::always_inline]] inline void skip<Shape>(uint8_t const *&code)
{
    auto const rank = take<uint8_t>(code);
    code += size_t{rank} * sizeof(uint16_t);
}

template <>
[[gnu::always_inline]] inline void skip<TensorType>(uint8_t const *&code)
{
    skip<Dtype>(code);
    skip<Shape>(code);
}

[[gnu::always_inline]] inline void
skip_bytes(uint8_t const *&code, size_t bytes)
{
    code += bytes;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
