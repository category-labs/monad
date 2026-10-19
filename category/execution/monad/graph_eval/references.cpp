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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/vm/code.hpp>
#include <category/vm/interpreter/intercode.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <span>
#include <tuple>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// A uint256 as a storage word or key, big-endian
bytes32_t to_word(uint256_t const &value)
{
    u256_be const be{value};
    bytes32_t word;
    std::memcpy(word.bytes, be.bytes, sizeof(word.bytes));
    return word;
}

// A storage word or key as a uint256
uint256_t to_uint256(bytes32_t const &word)
{
    return u256_be::unsafe_from(word.bytes).native();
}

// The number of 32-byte slots `size` bytes take
uint64_t slots_for(uint64_t const size)
{
    return (size + 31) / 32;
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<void> load_code_tensor(
    State &state, CodeRef const &ref, ByteOrder const order, Tensor &out)
{
    vm::SharedVarcode const varcode = state.get_code(ref.address);
    std::span<uint8_t const> code = varcode->intercode()->code_span();
    if (ref.offset == 0 || ref.offset >= code.size() || code[0] != 0x00) {
        return GraphEvalError::InvalidTensorRef;
    }
    code = code.subspan(ref.offset);
    auto const tensor =
        read_next<std::tuple<TensorType, std::span<uint8_t const>>>(code);
    if (tensor.has_error()) {
        return GraphEvalError::InvalidTensorRef;
    }
    auto const &[type, data] = tensor.value();
    if (type != out.type()) {
        return GraphEvalError::InvalidTensorRef;
    }
    // TODO: `order` applies to the elements only. Their header, before them,
    // is always little-endian, like the rest of the graphcode, which is a bit
    // of a quirk
    copy_elements(type.dtype(), order, data, out.data());
    return outcome::success();
}

Result<void> load_storage_tensor(
    CallerStorage &storage, StorageRef const &ref, ByteOrder const order,
    Tensor &out)
{
    Dtype const dtype = out.type().dtype();
    uint64_t const size = out.type().size_bytes();
    uint256_t const first = to_uint256(ref.slot);
    for (uint64_t i = 0; i < slots_for(size); i++) {
        bytes32_t const word = storage.load(to_word(first + i));
        // Elements are at most 8 bytes, so none straddles two slots
        uint64_t const offset = 32 * i;
        auto const n =
            static_cast<size_t>(std::min<uint64_t>(32, size - offset));
        copy_elements(dtype, order, {word.bytes, n}, out.data() + offset);
    }
    return outcome::success();
}

void store_storage_tensor(
    CallerStorage &storage, StorageRef const &ref, ByteOrder const order,
    Tensor const &tensor)
{
    Dtype const dtype = tensor.type().dtype();
    uint64_t const size = tensor.type().size_bytes();
    std::span<uint8_t const> const elements{
        tensor.data(), static_cast<size_t>(size)};
    uint256_t const first = to_uint256(ref.slot);
    for (uint64_t i = 0; i < slots_for(size); i++) {
        uint64_t const offset = 32 * i;
        auto const n =
            static_cast<size_t>(std::min<uint64_t>(32, size - offset));
        bytes32_t word{};
        copy_elements(
            dtype,
            order,
            elements.subspan(static_cast<size_t>(offset), n),
            word.bytes);
        // A slot whose word doesn't change isn't written, which saves State
        // the write. Loading it first adds no trie read, as State reads a
        // slot's original value to write it anyway
        bytes32_t const key = to_word(first + i);
        if (storage.load(key) != word) {
            storage.store(key, word);
        }
    }
}

bool storage_ranges_overlap(
    StorageRef const &a, uint64_t const a_size, StorageRef const &b,
    uint64_t const b_size)
{
    // Wrapping, like the slots
    uint256_t const a_to_b = to_uint256(b.slot) - to_uint256(a.slot);
    uint256_t const b_to_a = to_uint256(a.slot) - to_uint256(b.slot);
    return a_to_b < uint256_t{slots_for(a_size)} ||
           b_to_a < uint256_t{slots_for(b_size)};
}

MONAD_GRAPH_EVAL_NAMESPACE_END
