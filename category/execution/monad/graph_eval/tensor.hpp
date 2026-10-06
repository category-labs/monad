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

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <array>
#include <cstdint>
#include <cstring>
#include <span>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

struct Shape
{
    uint8_t rank;
    std::array<uint16_t, 8> dimensions; // Indices are valid up to rank_-1

    Shape() = default;

    Shape(uint8_t rank, std::array<uint16_t, 8> const &dimensions)
        : rank(rank)
        , dimensions(dimensions)
    {
    }

    constexpr uint64_t size() const noexcept
    {
        uint64_t size = 1;
        for (size_t i = 0; i < rank; ++i) {
            size *= dimensions[i];
        }
        return size;
    }
};

struct TensorType
{
    Dtype dtype;
    Shape shape;

    constexpr size_t size_bytes() const noexcept
    {
        return shape.size() * dtype_size(dtype);
    }
};

// Solidity:
// struct Tensor {
//     uint8 dtype;
//     uint16[] dimensions;
//     bytes data;
// }
class Tensor
{
    TensorType type_;
    uint8_t *data_; // Row-major, elements in host byte order

public:
    Tensor() = default;

    Tensor(TensorType type, uint8_t *data)
        : type_(type)
        , data_(data)
    {
    }

    constexpr TensorType const & type() const noexcept { return type_; }

    constexpr uint8_t *data() const noexcept
    {
        return data_;
    }

    // Return a view of this tensor's elements, as the C++ type matching its dtype
    template <typename T>
    constexpr std::span<T> elements() const
    {
        MONAD_DEBUG_ASSERT(type().dtype == dtype_of<std::remove_const_t<T>>());
        return {reinterpret_cast<T *>(data()), type().shape.size()};
    }
};

// A Tensor as abi_decode_tensor reads it from the calldata: its dtype and
// shape, and its data, still in place and big-endian
struct EncodedTensor
{
    Dtype dtype;
    Shape shape;
    byte_string_view data;
};

// The size in bytes of a tensor's data, or ShapeError if that overflows
Result<uint64_t> tensor_size_bytes(Dtype dtype, Shape const &shape);

bool same_shape(Shape const &a, Shape const &b);

// The shape numpy broadcasts `shapes` to: they're matched from their last
// dimensions, and each of the result's dimensions is their common size along
// it, a shape being repeated along any dimension where its size is 1 or it has
// none. ShapeError if they don't broadcast together.
Result<Shape> broadcast_shape(std::span<Shape const> shapes);

Result<EncodedTensor> abi_decode_tensor(byte_string_view &enc);

// Copies an encoded tensor's elements to `data`, converting them to host order
void abi_load_tensor_data(EncodedTensor const &tensor, uint8_t *data);

// Append an ABI-encoded tensor to a returndata buffer
void abi_append_tensor(Tensor const &tensor, byte_string &out);

MONAD_GRAPH_EVAL_NAMESPACE_END
