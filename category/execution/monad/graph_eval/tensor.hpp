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
#include <cstring>

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

// Solidity:
// struct Tensor {
//     uint8 dtype;
//     uint16[] dimensions;
//     bytes data;
// }
class Tensor
{
    Dtype dtype_;
    Shape shape_;
    uint8_t *data_; // Row-major, elements in host byte order

public:
    Tensor() = default;

    Tensor(Dtype dtype, Shape shape, uint8_t *data)
        : dtype_(dtype)
        , shape_(shape)
        , data_(data)
    {
    }

    constexpr uint64_t size_bytes() const noexcept
    {
        return dtype_size(dtype_) * shape_.size();
    }

    constexpr Shape const &shape() const noexcept
    {
        return shape_;
    }

    constexpr uint8_t rank() const noexcept
    {
        return shape_.rank;
    }

    constexpr std::array<uint16_t, 8> const &dimensions() const noexcept
    {
        return shape_.dimensions;
    }

    constexpr uint8_t *data() const noexcept
    {
        return data_;
    }

    constexpr Dtype dtype() const noexcept
    {
        return dtype_;
    }

    // Return a view of this tensor's elements, as the C++ type matching its dtype
    template <typename T>
    constexpr std::span<T> elements() const
    {
        MONAD_DEBUG_ASSERT(dtype() == dtype_of<std::remove_const_t<T>>());
        return {reinterpret_cast<T *>(data()), shape().size()};
    }
};

Result<Tensor> abi_decode_tensor(byte_string_view &enc);

// Append an ABI-encoded tensor to a returndata buffer
void abi_append_tensor(Tensor const &tensor, byte_string &out);

MONAD_GRAPH_EVAL_NAMESPACE_END
