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

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

class CompiledGraph
{
public:
};

class Compiler
{
    Graphcode const &gc_;
    std::span<uint8_t const> code_;

    iree_compiler_session_t *const session_;

    MlirContext ctx_;

    MlirType mlir_type(Dtype);
    MlirType mlir_type(TensorType const &);

    MlirStringRef mlir_string(std::string_view const);

    MlirNamedAttribute mlir_named(std::string_view const, MlirAttribute);

    MlirValue mlir_op(
        LiteralOp const &, MlirLocation loc, MlirBlock block,
        std::vector<MlirValue> const &);
    MlirValue mlir_op(
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

public:
    Result<CompiledGraph> compile();
    explicit Compiler(Graphcode const &gc);
    ~Compiler();
    Compiler(Compiler const &) = delete;
    Compiler(Compiler &&) = delete;
    Compiler &operator=(Compiler const &) = delete;
    Compiler &operator=(Compiler &&) = delete;
};

MONAD_GRAPH_EVAL_NAMESPACE_END
