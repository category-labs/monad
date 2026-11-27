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

#include <algorithm>
#include <array>
#include <concepts>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <variant>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

struct BroadcastLoop
{
    std::array<uint64_t, MAX_RANK> strides;
};

struct Shape
{
    constexpr Shape() noexcept
        : rank_(0)
        , dimensions_{}
        , size_(1)
    {
    }

    constexpr uint8_t rank() const noexcept
    {
        return rank_;
    }

    constexpr std::array<uint16_t, MAX_RANK> const &dimensions() const noexcept
    {
        return dimensions_;
    }

    constexpr size_t size() const noexcept
    {
        return size_;
    }

    constexpr bool operator==(Shape const &other) const noexcept
    {
        if (rank() != other.rank()) {
            return false;
        }
        return std::memcmp(
                   dimensions().data(),
                   other.dimensions().data(),
                   sizeof(dimensions()[0]) * rank()) == 0;
    }

    constexpr bool operator!=(Shape const &other) const noexcept = default;

    static constexpr Result<Shape> checked(
        uint8_t rank, std::array<uint16_t, MAX_RANK> const &dimensions) noexcept
    {
        if (rank > MAX_RANK) {
            return GraphEvalError::RankError;
        }
        size_t size = 1;
        for (size_t i = 0; i < rank; ++i) {
            if (MONAD_UNLIKELY(
                    __builtin_mul_overflow(size, dimensions[i], &size))) {
                return GraphEvalError::ShapeError;
            }
        }
        return Shape(rank, dimensions, size);
    }

    [[gnu::always_inline]]
    constexpr Result<BroadcastLoop> broadcast_to(Shape const &out_shape) const
    {
        uint8_t const in_rank = rank();
        uint8_t const out_rank = out_shape.rank();
        if (in_rank > out_rank) {
            return GraphEvalError::ShapeError;
        }
        BroadcastLoop loop{};
        uint64_t stride = 1;
        for (size_t i = in_rank; i-- > 0;) {
            size_t const d = out_rank - in_rank + i;
            uint16_t const size = dimensions()[i];
            if (size != 1) {
                if (size != out_shape.dimensions()[d]) {
                    return GraphEvalError::ShapeError;
                }
                loop.strides[d] = stride;
            }
            stride *= size;
        }
        return loop;
    }

private:
    uint8_t rank_;
    std::array<uint16_t, MAX_RANK>
        dimensions_; // Indices are valid up to rank_-1
    size_t size_;

    constexpr Shape(
        uint8_t rank, std::array<uint16_t, 8> const &dimensions,
        size_t size) noexcept
        : rank_(rank)
        , dimensions_(dimensions)
        , size_(size)
    {
    }
};

struct TensorType
{
    constexpr TensorType() noexcept
        : TensorType(Dtype::int8, Shape(), 1)
    {
    }

    constexpr Dtype dtype() const noexcept
    {
        return dtype_;
    }

    constexpr Shape const &shape() const noexcept
    {
        return shape_;
    }

    constexpr size_t size_bytes() const noexcept
    {
        return size_bytes_;
    }

    static constexpr Result<TensorType>
    checked(Dtype dtype, Shape shape) noexcept
    {
        auto size_bytes = shape.size();
        if (MONAD_UNLIKELY(__builtin_mul_overflow(
                size_bytes, dtype_size(dtype), &size_bytes))) {
            return GraphEvalError::ShapeError;
        }
        return TensorType(dtype, shape, size_bytes);
    }

    constexpr bool operator==(TensorType const &other) const noexcept
    {
        return dtype() == other.dtype() && shape() == other.shape();
    }

    constexpr bool operator!=(TensorType const &other) const noexcept = default;

private:
    Dtype dtype_;
    Shape shape_;
    size_t size_bytes_;

    constexpr TensorType(Dtype dtype, Shape shape, size_t size_bytes) noexcept
        : dtype_(dtype)
        , shape_(shape)
        , size_bytes_(size_bytes)
    {
    }
};

// Solidity:
// struct TensorType {
//     uint8 dtype;
//     uint16[] dimensions;
// }
// struct Tensor {
//     TensorType ty;
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

    constexpr TensorType const &type() const noexcept
    {
        return type_;
    }

    constexpr uint8_t *data() const noexcept
    {
        return data_;
    }

    template <typename T>
    constexpr std::span<T> elements() const
    {
        MONAD_DEBUG_ASSERT(
            type().dtype() == dtype_of<std::remove_const_t<T>>());
        return {reinterpret_cast<T *>(data()), type().shape().size()};
    }
};

// A graph's outputs, which point into the arena, in an array, so that returning
// them allocates nothing
struct GraphOutputs
{
    std::array<Tensor, MAX_GRAPH_OUTPUTS> tensors{};
    size_t count = 0;

    size_t size() const
    {
        return count;
    }

    Tensor const &operator[](size_t const i) const
    {
        return tensors[i];
    }

    Tensor const *begin() const
    {
        return tensors.data();
    }

    Tensor const *end() const
    {
        return tensors.data() + count;
    }
};

// The byte order of a tensor's elements outside the interpreter: big-endian in
// the calldata and the returned data, little-endian in an account's code.
// Inside, they're in host order
enum class ByteOrder : uint8_t
{
    BigEndian = 0,
    LittleEndian = 1,
};

// Where a TensorInput's elements are
enum class Location : uint8_t
{
    Literal = 0, // In the calldata
    Code = 1, // In an account's code, as for a TensorRef node
    Last_valid = Code,
};

// A tensor's elements in an account's code, from a byte offset counted from
// the code's first byte, as EXTCODECOPY counts
struct CodeRef
{
    Address address;
    uint32_t offset;
};

// Solidity:
// struct TensorInput {
//     TensorType ty;
//     Location location;
//     bytes payload;
// }
// The payload is the elements, big-endian, for a literal, and
// abi.encode(address, uint32 offset) for a CodeRef, whose elements in the code
// are little-endian. As abi_decode_tensor_input reads it from the calldata, a
// literal's elements are still in place there
struct TensorInput
{
    TensorType type;
    std::variant<byte_string_view, CodeRef> source;
};

// ABI-decode a T, a uint narrower than 256 bits or an address, from a whole
// word: InvalidInput if the word's value doesn't fit in T. abi_decode_fixed
// ignores the bytes above T, which the canonical encoding sets to zero
template <typename T>
    requires(BigEndianType<T> || std::same_as<T, Address>)
Result<T> abi_decode_fixed_checked(byte_string_view &enc)
{
    static_assert(sizeof(T) < 32);
    BOOST_OUTCOME_TRY(auto const word, abi_decode_fixed<u256_be>(enc));
    constexpr size_t high_size = 32 - sizeof(T);
    if (MONAD_UNLIKELY(std::any_of(
            word.bytes, word.bytes + high_size, [](uint8_t const b) {
                return b != 0;
            }))) {
        return GraphEvalError::InvalidInput;
    }
    T value{};
    std::memcpy(value.bytes, word.bytes + high_size, sizeof(T));
    return value;
}

// ABI-decode a TensorInput tuple. Only the canonical layout is accepted.
// InvalidInput if the dtype or a dimension doesn't fit its type, a tag isn't
// one of its values, a payload's padding isn't zero or a payload isn't what its
// location takes, ShapeError if a literal's elements don't have the size its
// type gives, and TypeError, RankError or ShapeError for an invalid type
Result<TensorInput> abi_decode_tensor_input(byte_string_view &enc);

// Copies the elements in `src`, of type `dtype`, to `dst`, converting them
// between `order` and host order. The conversion is its own inverse, so this
// works in either direction
void copy_elements(
    Dtype dtype, ByteOrder order, std::span<uint8_t const> src, uint8_t *dst);

// Append an ABI-encoded Tensor to a returndata buffer, with its elements
// big-endian
void abi_append_tensor(Tensor const &tensor, byte_string &out);

MONAD_GRAPH_EVAL_NAMESPACE_END
