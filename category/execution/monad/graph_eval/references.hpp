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

// Tensors read and written by reference: in an account's code, for TensorRef
// nodes and code inputs, and in contiguous slots of the caller's storage, for
// storage inputs and outputs

#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <cstdint>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// The storage of the account that called the precompile with DELEGATECALL,
// which storage references are to
class CallerStorage
{
public:
    virtual ~CallerStorage() = default;

    virtual bytes32_t load(bytes32_t const &slot) = 0;
    virtual void store(bytes32_t const &slot, bytes32_t const &value) = 0;
};

// Copies the tensor at `ref` in an account's code to `out`, in host order,
// from `order`. As in SSTORE2, the code is a 0x00 byte, so that calling the
// account stops at once, then the data: tensors encoded as a Literal's
// parameters, one after another, so the first is at offset 1. The one at the
// offset must have `out`'s type. InvalidTensorRef if it doesn't, if the code
// doesn't start with 0x00, or if the offset is 0 or leaves no room for the
// whole tensor
Result<void>
load_code_tensor(State &, CodeRef const &ref, ByteOrder order, Tensor &out);

// Copies the elements in the caller's storage from `ref`'s slot on to `out`,
// in host order, from `order`. They're packed in order, 32 bytes to a slot,
// each slot's first byte its most significant, so they take ceil(size / 32)
// contiguous slots, and the bytes past them in the last one are ignored.
//
// TODO: decide whether the slots start with the tensor's length, as a Solidity
// bytes value's do. For now they don't: the MNIST model's four tensors take
// 125 slots, which fit in one 128-slot MIP-8 page, but would take 129 with a
// length slot each. Without one, any slots hold a tensor of any type, so this
// can't fail, but it returns a Result for when it can
Result<void> load_storage_tensor(
    CallerStorage &, StorageRef const &ref, ByteOrder order, Tensor &out);

// Stores `tensor`'s elements in the caller's storage from `ref`'s slot on, in
// `order`, as load_storage_tensor reads them, with the bytes past them in the
// last slot zero. Slots whose words don't change aren't written
void store_storage_tensor(
    CallerStorage &, StorageRef const &ref, ByteOrder order,
    Tensor const &tensor);

// Whether the slots tensors of `a_size` and `b_size` bytes take from `a`'s and
// `b`'s slots overlap. Slots wrap around at 2^256
bool storage_ranges_overlap(
    StorageRef const &a, uint64_t a_size, StorageRef const &b, uint64_t b_size);

MONAD_GRAPH_EVAL_NAMESPACE_END
