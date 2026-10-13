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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
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
#include <optional>
#include <span>
#include <variant>

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

// The byte order of a tensor's elements outside the interpreter: in the
// calldata, in an account's code or in storage. Inside, they're in host order
enum class ByteOrder : uint8_t
{
    BigEndian = 0,
    LittleEndian = 1,
    Last_valid = LittleEndian,
};

// Where a TensorInput's elements are, or where a TensorOutput's go
enum class Location : uint8_t
{
    Literal = 0, // In the calldata, or for an output, the return data
    Code = 1, // In an account's code, as for a TensorRef node
    Storage = 2, // In contiguous slots of the caller's storage
    Last_valid = Storage,
};

// A tensor in an account's code, at a byte offset counted from the code's
// first byte, as EXTCODECOPY counts
struct CodeRef
{
    Address address;
    uint32_t offset;
};

// A tensor's elements in the caller's storage, in the contiguous slots from
// this one on, as load_storage_tensor reads them
struct StorageRef
{
    bytes32_t slot;
};

// Solidity:
// struct TensorInput {
//     uint8 dtype;
//     uint16[] dimensions;
//     uint8 byteOrder;
//     uint8 location;
//     bytes payload;
// }
// The payload is the elements for a literal, abi.encode(address, uint32
// offset) for a CodeRef, and abi.encode(uint256 slot) for a StorageRef. As
// abi_decode_tensor_input reads it from the calldata, a literal's elements are
// still in place there
struct TensorInput
{
    TensorType type;
    ByteOrder byte_order;
    std::variant<byte_string_view, CodeRef, StorageRef> source;
};

// Solidity:
// struct TensorOutput {
//     uint8 byteOrder;
//     uint8 location;
//     bytes payload;
// }
// An output is returned by value, for a literal, whose payload is empty, or
// stored, for a StorageRef, whose payload is abi.encode(uint256 slot)
struct TensorOutput
{
    ByteOrder byte_order;
    // Where the output is stored, or none if it's returned
    std::optional<StorageRef> destination;
};

// The size in bytes of a tensor's data, or ShapeError if that overflows
Result<uint64_t> tensor_size_bytes(Dtype dtype, Shape const &shape);

bool same_shape(Shape const &a, Shape const &b);

// The shape numpy broadcasts `shapes` to: they're matched from their last
// dimensions, and each of the result's dimensions is their common size along
// it, a shape being repeated along any dimension where its size is 1 or it has
// none. ShapeError if they don't broadcast together.
Result<Shape> broadcast_shape(std::span<Shape const> shapes);

// ABI-decode a TensorInput or a TensorOutput tuple. Only the canonical layout
// is accepted. InvalidInput if a tag isn't one of its values, or a payload
// isn't what its location takes, ShapeError if a literal's elements don't have
// the size its type gives, and TypeError, RankError or ShapeError for an
// invalid type
Result<TensorInput> abi_decode_tensor_input(byte_string_view &enc);
Result<TensorOutput> abi_decode_tensor_output(byte_string_view &enc);

// Copies the elements in `src`, of type `dtype`, to `dst`, converting them
// between `order` and host order. The conversion is its own inverse, so this
// works in either direction
void copy_elements(
    Dtype dtype, ByteOrder order, std::span<uint8_t const> src, uint8_t *dst);

// Append an ABI-encoded tensor to a returndata buffer, with its elements in
// `order`
void abi_append_tensor(Tensor const &tensor, ByteOrder order, byte_string &out);

MONAD_GRAPH_EVAL_NAMESPACE_END
