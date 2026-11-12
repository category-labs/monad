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
#include <category/execution/monad/graph_eval/broadcasting.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/lite_compiler.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// Fused graph code, in host byte order:
//   uint16 magic, FUSED_MAGIC
//   uint8 n_inputs, then each input's TensorType
//   uint8 n_outputs, then each output's node id (uint16)
//   uint16 n_ops, then the ops
// The inputs are nodes 0 to n_inputs - 1, and each op's result is the next
// node. An op is a FusedCore and its parameters, then a uint8 count of
// instructions, then the instructions: each a FusedInstruction and its
// parameters. The instructions are a stack program, evaluated at each element
// of the op's result, which is the one value they leave on the stack. The
// result has the core's shape, or, for a Map, the shape the Inputs broadcast
// to, and every Input and Gather must broadcast to it. A Reshape has no
// instructions: its result is its node's memory, under another shape.
//
// Some cores are computed whole at an op's first chunk, into memory of their
// own, before the instructions run on its chunks: MatMulEager and
// QMatMulEager, as the reference interpreter's MatMul and QMatMul ops compute
// their products; CumSumEager, ArgMaxEager, ReduceSumEager and
// ReduceMaxEager, by the evaluation of the reference interpreter's CumSum,
// ArgMax, ReduceSum and ReduceMax ops; Gather, by its Gather op's; Literal,
// TensorRef and Concat. An op
// whose one instruction is Core has its whole core computed into its result
// instead. The other cores are computed as the instructions run: MatMul and
// QMatMul a chunk of whole rows at a time, CumSum, ReduceSum and ReduceMax a
// chunk of results at a time, and ArgMax at the op's one chunk.
//
// A step that fails ends the run with its error, as the op it computes would
// fail in the reference interpreter: QDiv by zero, QInvSqrt of what isn't
// positive, a Gather's index out of range, a TensorRef whose tensor can't be
// read
constexpr uint16_t FUSED_MAGIC = 0x7ffd;

enum class FusedCore : uint8_t
{
    Map, // No core
    CumSum, // uint8 axis, uint16 node id: as the CumSum op
    MatMul, // uint16 node ids of x and y: as the MatMul op
    ArgMax, // uint16 node id: as the ArgMax op
    Reshape, // Shape, uint16 node id: as the Reshape op
    MatMulEager, // uint16 node ids of x and y: as the MatMul op
    Literal, // A Literal op's parameters: its TensorType, then the elements
    TensorRef, // A TensorRef op's: TensorType, 20-byte address, uint32 offset
    QMatMul, // uint8 bits, Dtype, uint16 node ids of x and y: as QMatMul
    QMatMulEager, // As QMatMul
    ReduceSum, // uint8 axis, uint16 node id: as the ReduceSum op
    ReduceMax, // uint8 axis, uint16 node id: as the ReduceMax op
    Concat, // uint8 axis, uint16 node ids of a and b: as the Concat op
    CumSumEager, // As CumSum
    ArgMaxEager, // As ArgMax
    ReduceSumEager, // As ReduceSum
    ReduceMaxEager, // As ReduceMax
    // uint8 axis, uint16 node ids of data and indices: as the Gather op, for
    // any Gather, where the Gather instruction reads one slice
    Gather,
    Last_valid = Gather,
};

enum class FusedInstruction : uint8_t
{
    Core, // Pushes the core's result
    Input, // uint16 node id: pushes the node's element
    Constant, // Dtype, then an element of it: pushes the element
    Sub, // Pops y, then x, and pushes x - y, as the Sub op
    Greater, // Pops y, then x, and pushes x > y, as the Greater op
    Where, // Pops y, x, then a condition, and pushes x or y, as the Where op
    Add, // Pops y, then x, and pushes x + y, as the Add op
    Mul, // Pops y, then x, and pushes x * y, as the Mul op
    Max, // Pops y, then x, and pushes the larger, as the Max op
    Min, // Pops y, then x, and pushes the smaller, as the Min op
    Div, // int64 denominator: pops x, and pushes the quotient, as the Div op
    Saturate, // Dtype: pops x, and pushes it converted, as the Saturate op
    QMul, // uint8 bits: pops y, then x, and pushes them as the QMul op does
    QDiv, // uint8 bits: pops y, then x, and pushes them as the QDiv op does
    QExp, // uint8 bits: pops x, and pushes it as the QExp op does
    QInvSqrt, // uint8 bits: pops x, and pushes it as the QInvSqrt op does
    Ge, // Pops y, then x, and pushes x >= y, as the Ge op
    Equal, // Pops y, then x, and pushes x == y, as the Equal op
    // uint16 node ids of data and indices, uint8 axis: pushes the element of
    // the Gather op's result, which must have one index, along an axis before
    // which every dimension of the data is 1, so that the result is one
    // contiguous slice of the data
    Gather,
    ISqrt, // Pops x, of an unsigned dtype, and pushes it as the ISqrt op does
    Last_valid = ISqrt,
};

constexpr size_t MAX_FUSED_INSTRUCTIONS = 32;

// Whether the core is computed whole, at its op's first chunk
constexpr bool is_whole_core(FusedCore const core)
{
    return core == FusedCore::MatMulEager || core == FusedCore::QMatMulEager ||
           core == FusedCore::CumSumEager || core == FusedCore::ArgMaxEager ||
           core == FusedCore::ReduceSumEager ||
           core == FusedCore::ReduceMaxEager || core == FusedCore::Literal ||
           core == FusedCore::TensorRef || core == FusedCore::Concat ||
           core == FusedCore::Gather;
}

// Whether the instruction's parameter is a uint8 count of fractional bits
constexpr bool has_fractional_bits(FusedInstruction const opcode)
{
    return opcode == FusedInstruction::QMul ||
           opcode == FusedInstruction::QDiv ||
           opcode == FusedInstruction::QExp ||
           opcode == FusedInstruction::QInvSqrt;
}

// How many elements of an op's result each of its steps computes at a time.
// A MatMul's steps compute whole rows, as many as fit, or one. A MatMulEager's
// product is computed whole, at the first chunk
constexpr uint64_t FUSED_CHUNK = 256;

// Where a step reads or writes the elements of a chunk
struct FusedOperand
{
    Place place;
    // How far the chunk's elements move per element of its start, in bytes:
    // the element size for a tensor, 0 for a chunk buffer or a constant
    uint32_t advance;
    // Whether the chunk's elements are contiguous, or one element repeated
    bool stride;
};

// What a step reads and writes besides its operands' places: the memory's
// arenas, and the state, which TensorRef reads accounts' code from
struct FusedContext
{
    kernel_memory_arenas arenas;
    State *state;
};

struct FusedStep
{
    // Success, or the error that ends the run
    GraphEvalError (*run)(
        FusedStep const &, uint64_t start, uint64_t length, FusedContext &);
    std::array<FusedOperand, 3> inputs;
    FusedOperand output;
    // A broadcast Input's loops, the result's and the Input's
    BroadcastLoops<2> loops;
    // CumSum's input as blocks of `rows` rows of `inner` elements, with the
    // axis running down the rows. inputs[1] holds the running sums of a row.
    // MatMul's x as rows of `inner` elements, and y as `inner` rows of
    // `columns`. ArgMax's input as `inner` elements
    uint64_t rows;
    uint64_t inner;
    uint64_t columns;
    // Div's denominator, or the shift that divides by a power of two; a
    // fixed-point instruction's or QMatMul's fractional bits; a Literal's
    // size; the axis of CumSumEager, ReduceSumEager, ReduceMaxEager and the
    // Gather core
    int64_t parameter;
    // QMatMul's operands' and result's dtypes; a Gather's index's dtype
    Dtype dtype;
    Dtype out_dtype;
    // A TensorRef's tensor in an account's code, and its type. The input's
    // and the result's types of CumSumEager, ArgMaxEager, ReduceSumEager,
    // ReduceMaxEager and the Gather core, whose indices' type is index_type
    CodeRef ref;
    TensorType input_type;
    TensorType index_type;
    TensorType type;
};

class FusedGraph
{
    friend class FusedGraphCompiler;

    struct FusedOp
    {
        uint64_t size; // The result's number of elements
        uint64_t chunk; // How many its steps compute at a time
        std::vector<FusedStep> steps;
    };

    std::vector<FusedOp> ops_;
    // Each Constant's element, at the start of a uint64_t of its own
    std::vector<uint64_t> constants_;
    std::vector<uint32_t> input_offsets_;
    std::vector<uint32_t> output_offsets_;
    // The memory holds the tensors, then the steps' chunk buffers
    uint64_t tensors_size_ = 0;
    uint64_t memory_size_ = 0;

public:
    std::vector<uint32_t> const &input_offsets() const
    {
        return input_offsets_;
    }

    std::vector<uint32_t> const &output_offsets() const
    {
        return output_offsets_;
    }

    uint64_t memory_size() const
    {
        return memory_size_;
    }

    // run assumes inputs have been written at input_offsets() by the caller.
    // TensorRef cores read accounts' code from `state`, and fail without it
    Result<void> run(std::span<uint8_t> memory, State *state = nullptr);
};

class FusedGraphCompiler
{
    std::span<uint8_t const> code_;
    FusedGraph graph_;
    std::vector<TensorType> node_types_;
    std::vector<Place> node_places_;
    std::vector<size_t> outputs_;
    uint64_t region_size_ = 0;

    Result<void> read_code();
    Result<void> read_op();
    Result<Place> allocate(TensorType const &type);

    explicit FusedGraphCompiler(std::span<uint8_t const> code);

public:
    static Result<FusedGraph> compile(std::span<uint8_t const> code);

    FusedGraphCompiler(FusedGraphCompiler const &) = delete;
    FusedGraphCompiler(FusedGraphCompiler &&) = delete;
    FusedGraphCompiler &operator=(FusedGraphCompiler const &) = delete;
    FusedGraphCompiler &operator=(FusedGraphCompiler &&) = delete;
};

MONAD_GRAPH_EVAL_NAMESPACE_END
