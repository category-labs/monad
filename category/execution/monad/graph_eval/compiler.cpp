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

#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/ops.hpp"
#include <category/execution/monad/graph_eval/compiler.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <iostream>
#include <iree/base/api.h>
#include <iree/compiler/embedding_api.h>
#include <iree/compiler/mlir_interop.h>
#include <iree/hal/allocator.h>
#include <iree/hal/buffer.h>
#include <iree/hal/buffer_view.h>
#include <iree/hal/device.h>
#include <iree/runtime/call.h>
#include <iree/runtime/instance.h>
#include <iree/runtime/session.h>
#include <iree/vm/bytecode/archive.h>
#include <iree/vm/bytecode/module.h>
#include <iree/vm/module.h>
#include <mlir-c/AffineExpr.h>
#include <mlir-c/AffineMap.h>
#include <mlir-c/BuiltinAttributes.h>
#include <mlir-c/BuiltinTypes.h>
#include <mlir-c/Dialect/Linalg.h>
#include <mlir-c/IR.h>
#include <mlir-c/Support.h>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

constexpr std::array<char const *, 9> IREE_COMPILER_FLAGS{
    "--iree-hal-target-device=local",
    "--iree-hal-local-target-device-backends=llvm-cpu",
    "--iree-llvmcpu-target-triple=x86_64-unknown-linux-gnu",
    "--iree-llvmcpu-target-cpu=znver4",
    "--iree-opt-level=O2",
    "--iree-opt-data-tiling",
    "--iree-llvmcpu-debug-symbols=false",
    "--iree-vm-bytecode-module-strip-source-map=true",
    "--iree-vm-emit-polyglot-zip=false",
};

void check_iree(iree_compiler_error_t *const error)
{
    if (error) {
        std::cerr << ireeCompilerErrorGetMessage(error) << std::endl;
        MONAD_ASSERT(false);
    }
}

MlirDialect mlir_nonnull(MlirDialect dialect)
{
    MONAD_ASSERT(!mlirDialectIsNull(dialect));
    return dialect;
}

MlirAttribute mlir_nonnull(MlirAttribute attr)
{
    MONAD_ASSERT(!mlirAttributeIsNull(attr));
    return attr;
}

MlirOperation mlir_append(MlirBlock block, MlirOperationState *state)
{
    auto const op = mlirOperationCreate(state);
    MONAD_ASSERT(!mlirOperationIsNull(op));
    mlirBlockAppendOwnedOperation(block, op);
    return op;
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

MlirValue Compiler::mlir_op(
    LiteralOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &)
{
    auto const &[type, data] = op.params;
    auto const value_type = mlir_type(type);
    MlirNamedAttribute const value = mlir_named(
        "value",
        mlir_nonnull(mlirDenseElementsAttrRawBufferGet(
            value_type, type.size_bytes(), data.data())));
    MlirOperationState constant =
        mlirOperationStateGet(mlir_string("arith.constant"), loc);
    mlirOperationStateAddAttributes(&constant, 1, &value);
    mlirOperationStateAddResults(&constant, 1, &value_type);
    return mlirOperationGetResult(mlir_append(block, &constant), 0);
}

MlirValue Compiler::mlir_op(
    TensorRefOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    AddOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    SubOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    GreaterOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    GeOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    EqualOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ReshapeOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    WhereOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    CumSumOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    SaturateOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    MatMulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ArgMaxOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ArgMinOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ClipOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    MaxOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    MinOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    MulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    DivOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    CastOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ExpandOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    QMulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    QDivOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    QMatMulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ReduceSumOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ReduceMaxOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    QExpOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    QInvSqrtOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    GatherOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirValue Compiler::mlir_op(
    ConcatOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    (void)op;
    (void)loc;
    (void)block;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

MlirType Compiler::mlir_type(Dtype dtype)
{
    // TODO: cache this?
    return mlirIntegerTypeGet(
        ctx_, static_cast<unsigned int>(8 * dtype_size(dtype)));
}

MlirType Compiler::mlir_type(TensorType const &type)
{
    // TODO: maybe we should represent dimensions like this internally to begin
    // with
    std::array<int64_t, MAX_RANK> dimensions;
    for (size_t i = 0; i < type.shape().rank(); i++) {
        dimensions[i] = type.shape().dimensions()[i];
    }
    return mlirRankedTensorTypeGet(
        type.shape().rank(),
        dimensions.data(),
        mlir_type(type.dtype()),
        mlirAttributeGetNull());
}

MlirStringRef Compiler::mlir_string(std::string_view const s)
{
    return mlirStringRefCreate(s.data(), s.size());
}

MlirNamedAttribute
Compiler::mlir_named(std::string_view const name, MlirAttribute attr)
{
    return mlirNamedAttributeGet(
        mlirIdentifierGet(ctx_, mlir_string(name)), attr);
}

Result<CompiledGraph> Compiler::compile()
{
    if (gc_.validation_result() != GraphEvalError::Success) {
        return gc_.validation_result();
    }
    MlirLocation const loc = mlirLocationUnknownGet(ctx_);
    MlirModule const module = mlirModuleCreateEmpty(loc);

    // Read magic number
    BOOST_OUTCOME_TRY(read_next<uint16_t>(code_));

    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code_));

    std::vector<MlirType> input_types;
    std::vector<MlirLocation> input_locs;
    for (size_t id = 0; id < n_inputs; id++) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<TensorType>(code_));
        input_types.push_back(mlir_type(gc_.tensor_types()[id]));
        input_locs.push_back(loc);
    }
    MlirBlock const body = mlirBlockCreate(
        static_cast<intptr_t>(input_types.size()),
        input_types.data(),
        input_locs.data());
    MlirRegion const func_region = mlirRegionCreate();
    mlirRegionAppendOwnedBlock(func_region, body);

    BOOST_OUTCOME_TRY(read_next<uint8_t>(code_)); // n_outputs
    std::vector<MlirType> output_types;
    for (auto const &output_id : gc_.outputs()) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<uint16_t>(code_));
        output_types.push_back(mlir_type(gc_.tensor_types()[output_id]));
    }

    MlirType func_type = mlirFunctionTypeGet(
        ctx_,
        static_cast<intptr_t>(input_types.size()),
        input_types.data(),
        static_cast<intptr_t>(output_types.size()),
        output_types.data());

    MlirNamedAttribute const func_attrs[]{
        mlir_named(
            "sym_name", mlirStringAttrGet(ctx_, mlir_string("function"))),
        mlir_named("function_type", mlirTypeAttrGet(func_type)),
    };

    MlirOperationState func =
        mlirOperationStateGet(mlir_string("func.func"), loc);
    mlirOperationStateAddAttributes(&func, 2, func_attrs);
    mlirOperationStateAddOwnedRegions(&func, 1, &func_region);
    mlir_append(mlirModuleGetBody(module), &func);

    std::vector<MlirValue> mlir_tensors;
    mlir_tensors.reserve(gc_.tensor_types().size());

    for (size_t i = 0; i < n_inputs; i++) {
        auto const input_i =
            mlirBlockGetArgument(body, static_cast<intptr_t>(i));
        mlir_tensors.push_back(input_i);
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code_));

    for (size_t i = 0; i < n_ops; i++) {
        BOOST_OUTCOME_TRY(
            visit_next(code_, [&]<typename OpT>(OpT const &op) -> Result<void> {
                MlirValue const value = mlir_op(op, loc, body, mlir_tensors);
                mlir_tensors.push_back(value);
                return outcome::success();
            }));
    }

    return CompiledGraph{};
}

Compiler::Compiler(Graphcode const &gc)
    : gc_(gc)
    , code_(gc.code_span())
    , session_(ireeCompilerSessionCreate())
{
    check_iree(ireeCompilerSessionSetFlags(
        session_,
        static_cast<int>(IREE_COMPILER_FLAGS.size()),
        IREE_COMPILER_FLAGS.data()));
    ctx_ = ireeCompilerSessionBorrowContext(session_);
    mlir_nonnull(mlirContextGetOrLoadDialect(ctx_, mlir_string("func")));
    mlir_nonnull(mlirContextGetOrLoadDialect(ctx_, mlir_string("arith")));
    mlir_nonnull(mlirContextGetOrLoadDialect(ctx_, mlir_string("tensor")));
    mlir_nonnull(mlirContextGetOrLoadDialect(ctx_, mlir_string("linalg")));
}

MONAD_GRAPH_EVAL_NAMESPACE_END
