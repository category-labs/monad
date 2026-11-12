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

#include <category/core/result.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// Region code: the I4 region IR of LOWERING_IDEAS.md with a fixed menu of
// cores, run by a pure interpreter in one validation pass over the code, then
// one execution pass. Neither allocates heap memory, except State, when it
// loads an account that Code tensors are copied from for the first time.
//
// The code, in host byte order, packed: fields are read in place, at whatever
// alignment they have
//   uint16 magic, REGION_MAGIC, and uint16 version, REGION_VERSION
//   uint64 arena_bytes: the arena's first bytes, which hold the tensors
//   uint16 n_tensors, then n_tensors records of REGION_TENSOR_BYTES each:
//     uint8 kind (RegionTensorKind), uint8 dtype, uint8 rank,
//     uint16 dimensions[MAX_RANK] (those past the rank are ignored),
//     uint32 location: the graph input's index, or the byte offset in the
//     arena, a multiple of TENSOR_DATA_ALIGNMENT,
//     uint32 source: for a Code tensor, the index of its reference; for a
//     Literal tensor, the byte offset of its data in the literals
//   uint16 n_references, then n_references references of
//     REGION_REFERENCE_BYTES each: a 20-byte address, then a uint32 offset in
//     its code, as a CodeRef
//   uint32 literal_bytes, then the literals: Literal tensors' data
//   uint16 n_statements, then the statements, run in order, each its uint8
//     kind (RegionStatement), then
//     - for a Region, the region;
//     - for a Compose, a uint16 tensor id X, a uint8 n, then n tensor ids
//       (uint16): the parts, whose bytes tile X's exactly
//   uint8 n_outputs, then each output's tensor id (uint16)
//
// Code and Literal tensors are in the arena, as Arena tensors are, and are
// copied there before the statements run: a Code tensor from its reference, as
// load_code_tensor copies it, with little-endian elements, and a Literal
// tensor from the literals. Validation checks the Code tensors' types against
// the accounts' code. Neither may be stored.
//
// A Compose statement does nothing at run time. Once its parts have all been
// written, X has been too, as the parts' bytes are all of X's. They're written
// by earlier statements.
//
// A region: a header of REGION_HEADER_BYTES, the extents and loops, two
// tables that instructions refer to by index, then the instructions:
//   uint8 rank (at least 1), n_loops, core (RegionCore), core dimension,
//     n_views, n_constants, n_slots, the lengths in bytes of the term's
//     instructions and of the epilogue's, then a Contraction's fractional
//     bits and output dtype (both ignored for other cores)
//   rank extents (uint16): the iteration space
//   n_loops loops, outermost first: uint8 dimension, uint8 kind
//     (RegionLoopKind), uint16 tile length (0 for a Whole loop)
//   n_views views of 14 + 4 * rank bytes: uint16 tensor id, uint32 element
//     offset, a uint16 index tensor id (REGION_NO_INDEX for none), a uint32
//     index stride, a uint16 index count, then rank strides (uint32), in
//     elements: element (i_0, ..., i_rank-1) of the space is element
//     offset + k * index stride + sum(i_d * stride_d) of the tensor, in
//     row-major order, where k is the index tensor's one element, read when
//     the region starts. IndexError unless 0 <= k < index count. A stored view
//     has no index tensor. A Contraction's lhs and rhs are views 0 and 1
//   n_constants constants of REGION_CONSTANT_BYTES: uint8 dtype, then a
//     uint64 whose low bytes are the value
//   the term's instructions, then the epilogue's. Each is its uint8 opcode
//     (RegionOp), then only the bytes it uses:
//     - a uint8 destination (none for Yield): for Store, a view; for the
//       other ops, a slot or a view to store the result in, encoded as an
//       operand is;
//     - a uint8 parameter, for the ops that take one: the constant holding
//       Div's int64 denominator, Saturate's dtype, or the fractional bits of
//       QMul, QDiv, QExp and QInvSqrt;
//     - a byte per operand: its RegionOperand in the top 2 bits, and the
//       index of its slot, view or constant in the other 6 (0 for Core)
//
// Loops: each dimension of the space has either one Whole loop, or a Tile loop
// and, inside it, an Intra loop with the same tile length. The innermost loop
// is the chunk loop: programs run on up to REGION_CHUNK of its elements at a
// time. The core dimension's loops are either the innermost ones (a Whole loop,
// or a Tile loop and its Intra loop), so that each output has one accumulator,
// or one Whole loop right outside the chunk loop, so that a chunk's outputs
// have one accumulator each.
//
// Cores: the term runs at every point of the space and feeds the core. Sum,
// Max, Min, ArgMax and ArgMin reduce it along the core dimension, ArgMax and
// ArgMin to the index of the first largest or smallest element, wrapped to the
// term's dtype; the epilogue then runs once per output, and its views have
// stride 0 along the core dimension. PrefixSum keeps inclusive running sums
// along it, and the epilogue runs at every point. Sums wrap. Contraction
// computes QMatMul's result along it, then runs the epilogue as Sum does: lhs
// and rhs have the same integer dtype, their products are exact, their sum
// wraps at 128 bits, is shifted right by the fractional bits, rounding down,
// and wraps to the output dtype.
//
// Every tensor a region reads must be a graph input or have been stored in
// full by an earlier region: a Store's view must reach every element of its
// tensor exactly once. Within a region, the stored views' bytes may not overlap
// one another or any view the region reads.

constexpr uint16_t REGION_MAGIC = 0x7ffc;
constexpr uint16_t REGION_VERSION = 2;

constexpr size_t REGION_TENSOR_BYTES = 1 + 1 + 1 + 2 * MAX_RANK + 4 + 4;
constexpr size_t REGION_REFERENCE_BYTES = 20 + 4;
constexpr size_t REGION_HEADER_BYTES = 11;
constexpr size_t REGION_CONSTANT_BYTES = 1 + 8;

// A view's index tensor id when it has none
constexpr uint16_t REGION_NO_INDEX = 0xffff;

// The most elements a program runs on at a time
constexpr size_t REGION_CHUNK = 256;

constexpr size_t REGION_MAX_SLOTS = 16;
constexpr size_t REGION_MAX_INSTRUCTIONS = 32;
constexpr size_t REGION_MAX_VIEWS = 64;
constexpr size_t REGION_MAX_CONSTANTS = 64;

// The int8 contraction kernel's copies of its operands, reused across chunks
constexpr size_t REGION_PACK_BYTES = 64 * 1024;

// The interpreter's scratch, which follows the tensors in the arena: the slots,
// the accumulators, the core's values and the contraction kernel's copies
constexpr size_t REGION_SLOT_BYTES = REGION_CHUNK * sizeof(uint64_t);
constexpr size_t REGION_SCRATCH_BYTES =
    REGION_MAX_SLOTS * REGION_SLOT_BYTES + 3 * REGION_SLOT_BYTES +
    REGION_CHUNK * sizeof(int32_t) + REGION_PACK_BYTES;

enum class RegionTensorKind : uint8_t
{
    Input,
    Arena,
    Code,
    Literal,
    Last_valid = Literal,
};

enum class RegionStatement : uint8_t
{
    Region,
    Compose,
    Last_valid = Compose,
};

enum class RegionLoopKind : uint8_t
{
    Whole,
    Tile,
    Intra,
    Last_valid = Intra,
};

enum class RegionCore : uint8_t
{
    None,
    Contraction,
    PrefixSum,
    Sum,
    Max,
    Min,
    ArgMax,
    ArgMin,
    Last_valid = ArgMin,
};

enum class RegionOp : uint8_t
{
    Add,
    Sub,
    Mul, // Widening, as the Mul op
    Div,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Max,
    Min,
    Saturate,
    Where,
    QMul,
    QDiv,
    QExp,
    QInvSqrt,
    Store,
    Yield,
    Last_valid = Yield,
};

enum class RegionOperand : uint8_t
{
    Slot,
    View,
    Constant,
    Core,
    Last_valid = Core,
};

struct RegionOutputs
{
    std::array<Tensor, MAX_GRAPH_OUTPUTS> tensors;
    size_t size;
};

// Benchmarking: the time of each part of the runs given it, summed over them,
// as ticks of the timestamp counter. `statements` is resized, which
// allocates, on the first run
struct RegionTimes
{
    uint64_t runs = 0;
    uint64_t total = 0; // The whole of run()
    uint64_t validation = 0;
    uint64_t loading = 0; // Copying the Code and Literal tensors
    std::vector<uint64_t> statements;
};

// Region code validated once, for running many times. Validation checks all
// that depends on the code alone. Each run checks the rest, which depends on
// the call: the inputs' types, against the Input tensors' records, and the
// arena; and the copying of each Code tensor checks the account's code, as
// load_code_tensor does. With RegionTimes, `validation` is each run's checks
class ValidatedRegionCode
{
    std::span<uint8_t const> code_;

    explicit ValidatedRegionCode(std::span<uint8_t const> const code)
        : code_(code)
    {
    }

public:
    // Validates `code`, which must outlive the result
    static Result<ValidatedRegionCode> validate(std::span<uint8_t const> code);

    // As RegionInterpreter::run, without validating the code again
    Result<RegionOutputs>
    run(std::span<uint8_t> arena, State &state, std::span<Tensor const> inputs,
        RegionTimes *times = nullptr) const;
};

class RegionInterpreter
{
public:
    // Validates `code` against `inputs`, the arena and the accounts' code in
    // `state`, then runs it. The outputs point into the arena. Adds the time
    // of each part of the run to `times`, if given
    static Result<RegionOutputs>
    run(std::span<uint8_t> arena, State &state, std::span<Tensor const> inputs,
        std::span<uint8_t const> code, RegionTimes *times = nullptr);
};

MONAD_GRAPH_EVAL_NAMESPACE_END
