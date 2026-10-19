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

#include "category/execution/monad/graph_eval/constants.hpp"
#include <category/core/math.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <algorithm>
#include <bit>
#include <cstring>

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

// A tag of a TensorInput or TensorOutput, a uint8 in the ABI: InvalidInput if
// its word isn't one of the tag's values
template <typename Tag>
Result<Tag> abi_decode_tag(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const word, abi_decode_fixed<u256_be>(enc));
    uint256_t const value = word.native();
    if (value > uint256_t{static_cast<uint8_t>(Tag::Last_valid)}) {
        return GraphEvalError::InvalidInput;
    }
    return static_cast<Tag>(value.as_words()[0]);
}

// The length of a dynamic value, a whole uint256, which must fit in 64 bits
Result<uint64_t> abi_decode_length(byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto const length_be, abi_decode_fixed<u256_be>(enc));
    uint256_t const length = length_be.native();
    if (length.as_words()[1] || length.as_words()[2] || length.as_words()[3]) {
        return GraphEvalError::InvalidInput;
    }
    return length.as_words()[0];
}

// The next `size` bytes of `enc`, which are padded with zeros to a multiple of
// 32 bytes, consuming the padding too
Result<byte_string_view>
abi_decode_padded_bytes(byte_string_view &enc, uint64_t const size)
{
    // Checking the size first bounds it by the input's length, so the rounding
    // below can't overflow
    if (MONAD_UNLIKELY(enc.size() < size)) {
        return AbiDecodeError::InputTooShort;
    }
    auto const padded_size = round_up<uint64_t>(size, 32);
    if (MONAD_UNLIKELY(enc.size() < padded_size)) {
        return AbiDecodeError::InputTooShort;
    }
    byte_string_view const data = enc.substr(0, static_cast<size_t>(size));
    enc.remove_prefix(static_cast<size_t>(padded_size));
    return data;
}

bool all_zero(byte_string_view const bytes)
{
    return std::all_of(
        bytes.begin(), bytes.end(), [](uint8_t const b) { return b == 0; });
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<TensorInput> abi_decode_tensor_input(byte_string_view &enc)
{
    // Static: uint8 dtype
    BOOST_OUTCOME_TRY(auto const dtype_be, abi_decode_fixed<u8_be>(enc));
    auto const dtype_id = dtype_be.native();
    if (dtype_id > static_cast<uint8_t>(Dtype::Last_valid_dtype)) {
        return GraphEvalError::TypeError;
    }
    auto const dtype = static_cast<Dtype>(dtype_id);

    // Dynamic: head(uint16[]), static: uint8 byteOrder and uint8 location,
    // then dynamic: head(bytes). The heads are the offsets of their tails from
    // the start of the tuple. The tails are read in place, so only the
    // canonical layout is accepted: the dimensions right after the five head
    // words, then the payload
    BOOST_OUTCOME_TRY(
        auto const dimensions_head, abi_decode_fixed<u256_be>(enc));
    BOOST_OUTCOME_TRY(auto const byte_order, abi_decode_tag<ByteOrder>(enc));
    BOOST_OUTCOME_TRY(auto const location, abi_decode_tag<Location>(enc));
    BOOST_OUTCOME_TRY(auto const payload_head, abi_decode_fixed<u256_be>(enc));

    // Dynamic: read tail(uint16[]), whose length, a whole uint256, is the rank
    BOOST_OUTCOME_TRY(auto const rank_be, abi_decode_fixed<u256_be>(enc));
    uint256_t const rank_256 = rank_be.native();
    if (rank_256.as_words()[1] || rank_256.as_words()[2] ||
        rank_256.as_words()[3] || rank_256.as_words()[0] > MAX_RANK) {
        return GraphEvalError::RankError;
    }
    auto const rank = static_cast<uint8_t>(rank_256.as_words()[0]);

    uint64_t const dimensions_offset = 5 * 32;
    uint64_t const payload_offset =
        dimensions_offset + 32 * (1 + uint64_t{rank});
    if (dimensions_head.native() != dimensions_offset ||
        payload_head.native() != payload_offset) {
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

    // Dynamic: read tail(bytes), the payload
    BOOST_OUTCOME_TRY(auto const payload_size, abi_decode_length(enc));
    if (MONAD_UNLIKELY(
            location == Location::Literal &&
            payload_size != expected_data_size)) {
        return GraphEvalError::ShapeError;
    }
    BOOST_OUTCOME_TRY(
        auto const payload, abi_decode_padded_bytes(enc, payload_size));

    BOOST_OUTCOME_TRY(Shape const shape, Shape::checked(rank, dimensions));
    BOOST_OUTCOME_TRY(TensorType const type, TensorType::checked(dtype, shape));
    switch (location) {
    case Location::Literal:
        return TensorInput{type, byte_order, payload};
    case Location::Code:
        // abi.encode(address, uint32): each a word, with its high bytes zero
        if (payload.size() != 64 || !all_zero(payload.substr(0, 12)) ||
            !all_zero(payload.substr(32, 28))) {
            return GraphEvalError::InvalidInput;
        }
        {
            CodeRef ref{};
            std::memcpy(ref.address.bytes, payload.data() + 12, 20);
            ref.offset = u32_be::unsafe_from(payload.data() + 60).native();
            return TensorInput{type, byte_order, ref};
        }
    case Location::Storage:
        // abi.encode(uint256 slot)
        if (payload.size() != 32) {
            return GraphEvalError::InvalidInput;
        }
        {
            StorageRef ref{};
            std::memcpy(ref.slot.bytes, payload.data(), 32);
            return TensorInput{type, byte_order, ref};
        }
    }
    MONAD_ABORT();
}

Result<TensorOutput> abi_decode_tensor_output(byte_string_view &enc)
{
    // Static: uint8 byteOrder and uint8 location, then dynamic: head(bytes),
    // which the canonical layout puts right after the three head words
    BOOST_OUTCOME_TRY(auto const byte_order, abi_decode_tag<ByteOrder>(enc));
    BOOST_OUTCOME_TRY(auto const location, abi_decode_tag<Location>(enc));
    // An output is returned, as a literal, or stored, but can't go to code
    if (location == Location::Code) {
        return GraphEvalError::InvalidInput;
    }
    BOOST_OUTCOME_TRY(auto const payload_head, abi_decode_fixed<u256_be>(enc));
    if (payload_head.native() != 3 * 32) {
        return GraphEvalError::InvalidInput;
    }

    // Dynamic: read tail(bytes), the payload: empty for a literal, and
    // abi.encode(uint256 slot) for storage
    BOOST_OUTCOME_TRY(auto const payload_size, abi_decode_length(enc));
    if (payload_size != (location == Location::Literal ? 0 : 32)) {
        return GraphEvalError::InvalidInput;
    }
    BOOST_OUTCOME_TRY(
        auto const payload, abi_decode_padded_bytes(enc, payload_size));
    TensorOutput output{byte_order, std::nullopt};
    if (location == Location::Storage) {
        output.destination.emplace();
        std::memcpy(output.destination->slot.bytes, payload.data(), 32);
    }
    return output;
}

void copy_elements(
    Dtype const dtype, ByteOrder const order,
    std::span<uint8_t const> const src, uint8_t *const dst)
{
    // Validators are x86, so host order is little-endian
    static_assert(std::endian::native == std::endian::little);

    // TODO: ensure all these loops get compiled to vectorized code.
    size_t const element_size = dtype_size(dtype);
    if (order == ByteOrder::LittleEndian || element_size == 1) {
        // An empty tensor's data may be null, and memcpy from null is UB even
        // for zero bytes
        if (!src.empty()) {
            std::memcpy(dst, src.data(), src.size());
        }
        return;
    }
    switch (element_size) {
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
        // Unreachable
        MONAD_ABORT();
    }
}

// Append an ABI-encoded tensor to a returndata buffer
void abi_append_tensor(
    Tensor const &tensor, ByteOrder const order, byte_string &out)
{
    uint64_t const encoded_tensor_head_size =
        32 /* dtype (uint8) */ + 32 /* head(uint16[]) */ + 32 /* head(bytes) */;
    uint64_t const encoded_dimensions_tail_size =
        32 /* size */ + 32 * tensor.type().shape().rank() /* dimensions */;
    auto const size_bytes = tensor.type().size_bytes();
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
    out += abi_encode_uint(u64_be{static_cast<uint8_t>(tensor.type().dtype())});
    out += abi_encode_uint(u64_be{dimensions_start});
    out += abi_encode_uint(u64_be{data_start});

    auto const &shape = tensor.type().shape();
    // Encode dimensions
    out += abi_encode_uint(u64_be{shape.rank()});
    for (auto i = 0; i < shape.rank(); i++) {
        out +=
            abi_encode_uint(u64_be{shape.dimensions()[static_cast<size_t>(i)]});
    }

    // Encode data, converting it from host order to `order` and padding it
    // with zeros to a multiple of 32 bytes. resize_and_overwrite writes it in
    // place, without zero-filling it first.
    out += abi_encode_uint(u64_be{size_bytes});
    size_t const data_offset = out.size();
    out.resize_and_overwrite(
        data_offset + padded_size_bytes, [&](uint8_t *buffer, size_t n) {
            uint8_t *const dst = buffer + data_offset;
            copy_elements(
                tensor.type().dtype(),
                order,
                {tensor.data(), static_cast<size_t>(size_bytes)},
                dst);
            std::memset(dst + size_bytes, 0, padded_size_bytes - size_bytes);
            return n;
        });
}

MONAD_GRAPH_EVAL_NAMESPACE_END
