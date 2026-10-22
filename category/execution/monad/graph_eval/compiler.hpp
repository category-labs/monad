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

#include "category/core/result.hpp"
#include "category/execution/monad/graph_eval/ops.hpp"
#include "category/execution/monad/graph_eval/types.hpp"
#include <category/core/address.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <iree/compiler/embedding_api.h>
#include <mlir-c/AffineExpr.h>
#include <mlir-c/BuiltinTypes.h>
#include <mlir-c/IR.h>

#include <cstdint>
#include <initializer_list>
#include <memory>
#include <span>
#include <string>
#include <string_view>
#include <utility>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// A graph Compiler compiled: an IREE module whose function takes the graph's
// inputs, then its outputs, which it writes in place, then the memory for the
// tensors it computes in between, called in an IREE session of its own on the
// local-sync device, which runs it on the calling thread. A session isn't
// thread-safe, so neither is run
class CompiledGraph
{
    friend class Compiler;

    struct Session; // compiler.cpp's
    std::unique_ptr<Session> session_;

    explicit CompiledGraph(std::unique_ptr<Session>);

public:
    CompiledGraph(CompiledGraph &&) noexcept;
    CompiledGraph &operator=(CompiledGraph &&) noexcept;
    ~CompiledGraph();

    // Runs the graph on `inputs`, each a dense row-major tensor of its
    // input's type, in host byte order, writing each output to the memory in
    // `outputs`, as the same. The tensors computed in between are in
    // `scratch`. Every input, output and scratch must be
    // TENSOR_DATA_ALIGNMENT-aligned, as IREE only imports host memory aligned
    // to IREE_HAL_HEAP_BUFFER_ALIGNMENT, the same 64 bytes. OutOfMemory if the
    // tensors in between don't fit, and InternalError if IREE fails otherwise
    Result<void>
    run(std::span<uint8_t const *const> inputs,
        std::span<uint8_t *const> outputs, std::span<uint8_t> scratch);
};

class Compiler
{
    Graphcode const &gc_;
    std::span<uint8_t const> code_;
    State &state_; // For the code that TensorRefs read

    iree_compiler_session_t *const session_;

    MlirContext ctx_;

    MlirType mlir_type(Dtype);
    MlirType mlir_type(TensorType const &);

    MlirStringRef mlir_string(std::string_view const);

    MlirNamedAttribute mlir_named(std::string_view const, MlirAttribute);

    MlirValue mlir_empty(MlirLocation, MlirBlock, MlirType);
    MlirValue mlir_constant(MlirLocation, MlirBlock, MlirType, __int128 value);
    MlirValue mlir_value(
        MlirLocation, MlirBlock, std::string_view name,
        std::initializer_list<MlirValue> operands, MlirType);
    MlirValue
    mlir_cmpi(MlirLocation, MlirBlock, int64_t predicate, MlirValue, MlirValue);
    std::pair<MlirValue, MlirValue> mlir_divide_narrow(
        MlirLocation, MlirBlock, MlirValue high, MlirValue low,
        MlirValue divisor);
    MlirValue
    mlir_isqrt(MlirLocation, MlirBlock, MlirValue high, MlirValue low);
    MlirValue
    mlir_fill(MlirLocation, MlirBlock, MlirValue value, MlirValue init);
    template <typename Body>
    MlirOperation mlir_generic(
        MlirLocation, MlirBlock, std::span<MlirValue const> inputs,
        std::span<MlirValue const> inits, std::span<MlirAttribute const> maps,
        std::span<MlirAttribute const> iterator_types, Body const &body);
    template <typename Body>
    MlirValue mlir_elementwise(
        MlirLocation, MlirBlock, std::span<size_t const> input_ids,
        std::vector<MlirValue> const &values, Body const &body);
    MlirValue mlir_compare(
        MlirLocation, MlirBlock, std::span<size_t const> input_ids,
        std::vector<MlirValue> const &values, int64_t signed_predicate,
        int64_t unsigned_predicate);
    MlirValue mlir_reduce(
        MlirLocation, MlirBlock, size_t axis, size_t input_id,
        std::vector<MlirValue> const &values, std::string_view combine,
        __int128 initial);

    MlirValue mlir_op(
        LiteralOp const &, MlirLocation loc, MlirBlock block,
        std::vector<MlirValue> const &);
    Result<MlirValue> mlir_op(
        TensorRefOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        AddOp const &, MlirLocation, MlirBlock, std::vector<MlirValue> const &);
    MlirValue mlir_op(
        SubOp const &, MlirLocation, MlirBlock, std::vector<MlirValue> const &);
    MlirValue mlir_op(
        GreaterOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        GeOp const &, MlirLocation, MlirBlock, std::vector<MlirValue> const &);
    MlirValue mlir_op(
        EqualOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ReshapeOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        WhereOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        CumSumOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        SaturateOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        MatMulOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ArgMaxOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ArgMinOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ClipOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        MaxOp const &, MlirLocation, MlirBlock, std::vector<MlirValue> const &);
    MlirValue mlir_op(
        MinOp const &, MlirLocation, MlirBlock, std::vector<MlirValue> const &);
    MlirValue mlir_op(
        MulOp const &, MlirLocation, MlirBlock, std::vector<MlirValue> const &);
    MlirValue mlir_op(
        DivOp const &, MlirLocation, MlirBlock, std::vector<MlirValue> const &);
    MlirValue mlir_op(
        CastOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ExpandOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        QMulOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        QDivOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        QMatMulOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ReduceSumOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ReduceMaxOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        QExpOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        QInvSqrtOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        GatherOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
        ConcatOp const &, MlirLocation, MlirBlock,
        std::vector<MlirValue> const &);

    Result<CompiledGraph> iree_compile(MlirModule, std::string *ir);

public:
    // Compiles the graph. If `ir` isn't null, it gets the MLIR module as
    // built, of linalg ops, and as IREE's pipeline leaves it, in its VM
    // dialect, for inspecting the code
    Result<CompiledGraph> compile(std::string *ir = nullptr);
    Compiler(Graphcode const &gc, State &state);
    ~Compiler();
    Compiler(Compiler const &) = delete;
    Compiler(Compiler &&) = delete;
    Compiler &operator=(Compiler const &) = delete;
    Compiler &operator=(Compiler &&) = delete;
};

MONAD_GRAPH_EVAL_NAMESPACE_END
