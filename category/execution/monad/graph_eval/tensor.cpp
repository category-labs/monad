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

#include <category/core/math.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <algorithm>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// Copies the elements of type T in `src` to `dst`, converting between host and
// big-endian order. The conversion is its own inverse, so this works in either
// direction.
template <typename T>
inline void
copy_big_endian(uint8_t *const dst, std::span<uint8_t const> const src)
{
    constexpr size_t element_size = sizeof(T);
    MONAD_DEBUG_ASSERT(src.size() % element_size == 0);
    for (size_t i = 0; i < src.size() / element_size; i++) {
        T value;
        std::memcpy(&value, src.data() + element_size * i, element_size);
        BigEndian<T> const value_be{value};
        std::memcpy(dst + element_size * i, value_be.bytes, element_size);
    }
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<uint64_t> tensor_size_bytes(Dtype const dtype, Shape const &shape)
{
    uint64_t size = dtype_size(dtype);
    for (size_t i = 0; i < shape.rank; i++) {
        if (MONAD_UNLIKELY(
                __builtin_mul_overflow(size, shape.dimensions[i], &size))) {
            return GraphEvalError::ShapeError;
        }
    }
    return size;
}

// A loop rather than std::equal, which GCC makes a call to memcmp
bool same_shape(Shape const &a, Shape const &b)
{
    if (a.rank != b.rank) {
        return false;
    }
    for (size_t d = 0; d < a.rank; d++) {
        if (a.dimensions[d] != b.dimensions[d]) {
            return false;
        }
    }
    return true;
}

Result<Shape> broadcast_shape(std::span<Shape const> const shapes)
{
    Shape result{};
    for (Shape const &shape : shapes) {
        result.rank = std::max(result.rank, shape.rank);
    }
    std::fill_n(result.dimensions.begin(), result.rank, uint16_t{1});
    for (Shape const &shape : shapes) {
        for (size_t i = 0; i < shape.rank; i++) {
            size_t const d = result.rank - shape.rank + i;
            uint16_t const size = shape.dimensions[i];
            if (size != 1) {
                if (result.dimensions[d] != 1 && result.dimensions[d] != size) {
                    return GraphEvalError::ShapeError;
                }
                result.dimensions[d] = size;
            }
        }
    }
    return result;
}

Result<EncodedTensor> abi_decode_tensor(byte_string_view &enc)
{
    // Static: uint8 dtype
    BOOST_OUTCOME_TRY(auto const dtype_be, abi_decode_fixed<u8_be>(enc));
    auto const dtype_id = dtype_be.native();
    if (dtype_id > static_cast<uint8_t>(Dtype::Last_valid_dtype)) {
        return GraphEvalError::TypeError;
    }
    auto const dtype = static_cast<Dtype>(dtype_id);

    // Dynamic: head(uint16[]) and head(bytes), the offsets of their tails from
    // the start of the tuple. The tails are read in place, so only the
    // canonical layout is accepted: the dimensions right after the three head
    // words, then the data
    BOOST_OUTCOME_TRY(
        auto const dimensions_head, abi_decode_fixed<u256_be>(enc));
    BOOST_OUTCOME_TRY(auto const data_head, abi_decode_fixed<u256_be>(enc));

    // Dynamic: read tail(uint16[]), whose length, a whole uint256, is the rank
    BOOST_OUTCOME_TRY(auto const rank_be, abi_decode_fixed<u256_be>(enc));
    uint256_t const rank_256 = rank_be.native();
    if (rank_256.as_words()[1] || rank_256.as_words()[2] ||
        rank_256.as_words()[3] || rank_256.as_words()[0] > 8) {
        return GraphEvalError::RankError;
    }
    auto const rank = static_cast<uint8_t>(rank_256.as_words()[0]);

    uint64_t const dimensions_offset = 3 * 32;
    uint64_t const data_offset = dimensions_offset + 32 * (1 + uint64_t{rank});
    if (dimensions_head.native() != dimensions_offset ||
        data_head.native() != data_offset) {
        return GraphEvalError::InvalidInput;
    }

    std::array<uint16_t, 8> dimensions{};
    // Size in bytes the data must have for this shape
    uint64_t expected_data_size = dtype_size(dtype);
    for (auto i = 0; i < rank; i++) {
        BOOST_OUTCOME_TRY(auto const dim_be, abi_decode_fixed<u16_be>(enc));
        uint16_t const dim = dim_be.native();
        dimensions[static_cast<size_t>(i)] = dim;
        if (MONAD_UNLIKELY(__builtin_mul_overflow(
                expected_data_size, dim, &expected_data_size))) {
            return GraphEvalError::ShapeError;
        }
    }

    // Dynamic: read tail(bytes)
    BOOST_OUTCOME_TRY(auto const data_size_be, abi_decode_fixed<u256_be>(enc));
    uint256_t const data_size_256 = data_size_be.native();
    if (data_size_256.as_words()[1] || data_size_256.as_words()[2] ||
        data_size_256.as_words()[3]) {
        return GraphEvalError::InvalidInput;
    }
    auto const data_size = data_size_256.as_words()[0];
    if (MONAD_UNLIKELY(data_size != expected_data_size)) {
        return GraphEvalError::ShapeError;
    }

    // Checking the size first bounds it by the input's length, so the rounding
    // below can't overflow
    if (MONAD_UNLIKELY(enc.size() < data_size)) {
        return AbiDecodeError::InputTooShort;
    }
    auto const padded_size = round_up<uint64_t>(data_size, 32);
    if (MONAD_UNLIKELY(enc.size() < padded_size)) {
        return AbiDecodeError::InputTooShort;
    }
    byte_string_view const data = enc.substr(0, static_cast<size_t>(data_size));
    enc.remove_prefix(static_cast<size_t>(padded_size));

    return EncodedTensor{dtype, Shape{rank, dimensions}, data};
}

void abi_load_tensor_data(EncodedTensor const &tensor, uint8_t *const data)
{
    // TODO: ensure all these loops get compiled to vectorized code.
    std::span<uint8_t const> const src{tensor.data};
    switch (dtype_size(tensor.dtype)) {
    case 1:
        // An empty input's data may be null, and memcpy from null is UB even
        // for zero bytes
        if (!src.empty()) {
            std::memcpy(data, src.data(), src.size());
        }
        break;
    case 2:
        copy_big_endian<uint16_t>(data, src);
        break;
    case 4:
        copy_big_endian<uint32_t>(data, src);
        break;
    case 8:
        copy_big_endian<uint64_t>(data, src);
        break;
    default:
        // Unreachable
        MONAD_ABORT();
    }
}

// Append an ABI-encoded tensor to a returndata buffer
void abi_append_tensor(Tensor const &tensor, byte_string &out)
{
    uint64_t const encoded_tensor_head_size =
        32 /* dtype (uint8) */ + 32 /* head(uint16[]) */ + 32 /* head(bytes) */;
    uint64_t const encoded_dimensions_tail_size =
        32 /* size */ + 32 * tensor.type().shape.rank /* dimensions */;
    uint64_t const size_bytes = tensor.type().size_bytes();
    uint64_t const padded_size_bytes = 32 * ((size_bytes + 31) / 32);
    uint64_t const encoded_data_tail_size =
        32 /* size */ + padded_size_bytes /* data */;
    uint64_t const encoded_tensor_tail_size =
        encoded_dimensions_tail_size + encoded_data_tail_size;
    auto const encoded_tensor_byte_size =
        encoded_tensor_head_size + encoded_tensor_tail_size;
    // TODO: can encoded_tensor_byte_size ever not fit in a size_t?
    out.reserve(out.size() + static_cast<size_t>(encoded_tensor_byte_size));

    uint64_t const dimensions_start = encoded_tensor_head_size;
    uint64_t const data_start =
        encoded_tensor_head_size + encoded_dimensions_tail_size;

    // Encode head
    out += abi_encode_uint(u64_be{static_cast<uint8_t>(tensor.type().dtype)});
    out += abi_encode_uint(u64_be{dimensions_start});
    out += abi_encode_uint(u64_be{data_start});

    auto const &shape = tensor.type().shape;
    // Encode dimensions
    out += abi_encode_uint(u64_be{shape.rank});
    for (auto i = 0; i < shape.rank; i++) {
        out +=
            abi_encode_uint(u64_be{shape.dimensions[static_cast<size_t>(i)]});
    }

    // Encode data, converting it from host to big-endian order and padding it
    // with zeros to a multiple of 32 bytes. resize_and_overwrite writes it in
    // place, without zero-filling it first.
    out += abi_encode_uint(u64_be{size_bytes});
    size_t const data_offset = out.size();
    out.resize_and_overwrite(
        data_offset + padded_size_bytes, [&](uint8_t *buffer, size_t n) {
            uint8_t *const dst = buffer + data_offset;
            std::span<uint8_t const> const src{
                tensor.data(), static_cast<size_t>(size_bytes)};
            switch (dtype_size(tensor.type().dtype)) {
            case 1:
                // An empty tensor's data may be null, and memcpy from null is
                // UB even for zero bytes
                if (size_bytes != 0) {
                    std::memcpy(dst, src.data(), src.size());
                }
                break;
            case 2:
                copy_big_endian<uint16_t>(dst, src);
                break;
            case 4:
                copy_big_endian<uint32_t>(dst, src);
                break;
            case 8:
                copy_big_endian<uint64_t>(dst, src);
                break;
            default:
                MONAD_ABORT();
            }
            std::memset(dst + size_bytes, 0, padded_size_bytes - size_bytes);
            return n;
        });
}

MONAD_GRAPH_EVAL_NAMESPACE_END
