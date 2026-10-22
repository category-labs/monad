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

#include "category/execution/monad/graph_eval/fixed_point.hpp"
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include "category/execution/monad/graph_eval/ops.hpp"
#include "category/execution/monad/graph_eval/references.hpp"
#include "category/execution/monad/graph_eval/tensor.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <category/execution/monad/graph_eval/compiler.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <charconv>
#include <concepts>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <iree/base/api.h>
#include <iree/compiler/embedding_api.h>
#include <iree/compiler/mlir_interop.h>
#include <iree/hal/allocator.h>
#include <iree/hal/buffer.h>
#include <iree/hal/buffer_view.h>
#include <iree/hal/device.h>
#include <iree/modules/hal/types.h>
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
#include <mutex>
#include <span>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

constexpr std::array<char const *, 10> IREE_COMPILER_FLAGS{
    "--iree-hal-target-device=local",
    "--iree-hal-local-target-device-backends=llvm-cpu",
    "--iree-llvmcpu-target-triple=x86_64-unknown-linux-gnu",
    "--iree-llvmcpu-target-cpu=znver4",
    "--iree-opt-level=O2",
    "--iree-opt-data-tiling",
    "--iree-llvmcpu-debug-symbols=false",
    "--iree-vm-bytecode-module-strip-source-map=true",
    "--iree-vm-emit-polyglot-zip=false",
    // IREE demotes f64 to f32 by default, but mlir_isqrt's estimate relies on
    // double precision
    "--iree-input-demote-f64-to-f32=false",
};

void check_iree(iree_compiler_error_t *const error)
{
    if (error) {
        std::cerr << ireeCompilerErrorGetMessage(error) << std::endl;
        MONAD_ASSERT(false);
    }
}

// A new compiler session. The compiler's process-wide state is set up before
// the first one, and never shut down: the last ireeCompilerGlobalShutdown
// disables the compiler for the rest of the process
iree_compiler_session_t *create_session()
{
    static std::once_flag initialized;
    std::call_once(initialized, ireeCompilerGlobalInitialize);
    return ireeCompilerSessionCreate();
}

// Whether `status` is OK, freeing it if it isn't
bool iree_ok(iree_status_t const status)
{
    if (iree_status_is_ok(status)) {
        return true;
    }
    iree_status_ignore(status);
    return false;
}

// The IREE runtime and its local-sync device, shared by every compiled
// graph's session. Created on first use and never destroyed, as kernel.cpp's
struct IreeDevice
{
    iree_runtime_instance_t *instance;
    iree_hal_device_t *device;
};

IreeDevice const &iree_device()
{
    static IreeDevice const device = [] {
        iree_runtime_instance_options_t options;
        iree_runtime_instance_options_initialize(&options);
        iree_runtime_instance_options_use_all_available_drivers(&options);
        IreeDevice device{};
        MONAD_ASSERT(iree_ok(iree_runtime_instance_create(
            &options, iree_allocator_system(), &device.instance)));
        MONAD_ASSERT(iree_ok(iree_runtime_instance_try_create_default_device(
            device.instance,
            iree_make_cstring_view("local-sync"),
            &device.device)));
        return device;
    }();
    return device;
}

iree_hal_element_type_t iree_element_type(Dtype const dtype)
{
    return IREE_HAL_ELEMENT_TYPE_VALUE(
        dtype_signed(dtype) ? IREE_HAL_NUMERICAL_TYPE_INTEGER_SIGNED
                            : IREE_HAL_NUMERICAL_TYPE_INTEGER_UNSIGNED,
        8 * dtype_size(dtype));
}

// `size` bytes of host memory at `data`, imported as a buffer of the
// session's device, without copying. Null if IREE fails, as it does if the
// memory isn't aligned
iree_hal_buffer_t *iree_import(
    iree_runtime_session_t *const session, uint8_t *const data,
    size_t const size)
{
    iree_hal_buffer_params_t params{};
    params.type = IREE_HAL_MEMORY_TYPE_DEVICE_LOCAL;
    params.access = IREE_HAL_MEMORY_ACCESS_ALL;
    params.usage = IREE_HAL_BUFFER_USAGE_DEFAULT;
    iree_hal_external_buffer_t external{};
    external.type = IREE_HAL_EXTERNAL_BUFFER_TYPE_HOST_ALLOCATION;
    external.size = size;
    external.handle.host_allocation.ptr = data;
    iree_hal_buffer_t *buffer = nullptr;
    if (!iree_ok(iree_hal_allocator_import_buffer(
            iree_runtime_session_device_allocator(session),
            params,
            &external,
            iree_hal_buffer_release_callback_null(),
            &buffer))) {
        return nullptr;
    }
    return buffer;
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

MlirType mlir_nonnull(MlirType type)
{
    MONAD_ASSERT(!mlirTypeIsNull(type));
    return type;
}

MlirOperation mlir_append(MlirBlock block, MlirOperationState *state)
{
    auto const op = mlirOperationCreate(state);
    MONAD_ASSERT(!mlirOperationIsNull(op));
    mlirBlockAppendOwnedOperation(block, op);
    return op;
}

// arith.cmpi's predicates, as arith::CmpIPredicate numbers them
constexpr int64_t CMPI_EQ = 0;
constexpr int64_t CMPI_NE = 1;
constexpr int64_t CMPI_SLT = 2;
constexpr int64_t CMPI_SLE = 3;
constexpr int64_t CMPI_SGT = 4;
constexpr int64_t CMPI_SGE = 5;
constexpr int64_t CMPI_ULT = 6;
constexpr int64_t CMPI_ULE = 7;
constexpr int64_t CMPI_UGT = 8;
constexpr int64_t CMPI_UGE = 9;

// The longest axis along which CumSum is a chain of an add per slice rather
// than a scan
constexpr uint64_t MAX_UNROLLED_CUMSUM = 16;

bool is_signed(Dtype const dtype)
{
    return visit_dtype(dtype, []<typename T>() { return std::is_signed_v<T>; });
}

// A linalg iterator type, parallel or reduction, which has no C API
// constructor
MlirAttribute iterator_type(MlirContext const ctx, bool const reduction)
{
    return mlir_nonnull(mlirAttributeParseGet(
        ctx,
        mlirStringRefCreateFromCString(
            reduction ? "#linalg.iterator_type<reduction>"
                      : "#linalg.iterator_type<parallel>")));
}

// An indexing map, from `n_loops` loop indices to `results`
MlirAttribute indexing_map(
    MlirContext const ctx, size_t const n_loops,
    std::span<MlirAffineExpr> const results)
{
    return mlirAffineMapAttrGet(mlirAffineMapGet(
        ctx,
        static_cast<intptr_t>(n_loops),
        0,
        static_cast<intptr_t>(results.size()),
        results.data()));
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// A tensor of `type` with unspecified elements, for an op that writes all of
// them
MlirValue Compiler::mlir_empty(
    MlirLocation const loc, MlirBlock const block, MlirType const type)
{
    MlirOperationState empty =
        mlirOperationStateGet(mlir_string("tensor.empty"), loc);
    mlirOperationStateAddResults(&empty, 1, &type);
    return mlirOperationGetResult(mlir_append(block, &empty), 0);
}

// A scalar of an integer type
MlirValue Compiler::mlir_constant(
    MlirLocation const loc, MlirBlock const block, MlirType const type,
    __int128 const value)
{
    // mlirIntegerAttrGet takes an int64, which it truncates to narrower types
    // and zero-extends to wider ones; a wider type gets the value's words.
    // `index` isn't an integer type, and mlirIntegerAttrGet handles it
    std::array<uint64_t, 2> const words{
        static_cast<uint64_t>(value), static_cast<uint64_t>(value >> 64)};
    MlirNamedAttribute const attr = mlir_named(
        "value",
        mlirTypeIsAInteger(type) && mlirIntegerTypeGetWidth(type) > 64
            ? mlirIntegerAttrGetFromWords(type, 2, words.data())
            : mlirIntegerAttrGet(type, static_cast<int64_t>(value)));
    MlirOperationState constant =
        mlirOperationStateGet(mlir_string("arith.constant"), loc);
    mlirOperationStateAddAttributes(&constant, 1, &attr);
    mlirOperationStateAddResults(&constant, 1, &type);
    return mlirOperationGetResult(mlir_append(block, &constant), 0);
}

// An op with `operands` and a result of `type`, appended to `block`
MlirValue Compiler::mlir_value(
    MlirLocation const loc, MlirBlock const block, std::string_view const name,
    std::initializer_list<MlirValue> const operands, MlirType const type)
{
    MlirOperationState state = mlirOperationStateGet(mlir_string(name), loc);
    mlirOperationStateAddOperands(
        &state, static_cast<intptr_t>(operands.size()), operands.begin());
    mlirOperationStateAddResults(&state, 1, &type);
    return mlirOperationGetResult(mlir_append(block, &state), 0);
}

// arith.cmpi, with one of the CMPI_ predicates
MlirValue Compiler::mlir_cmpi(
    MlirLocation const loc, MlirBlock const block, int64_t const predicate,
    MlirValue const lhs, MlirValue const rhs)
{
    MlirNamedAttribute const attr = mlir_named(
        "predicate",
        mlirIntegerAttrGet(mlirIntegerTypeGet(ctx_, 64), predicate));
    MlirType const i1 = mlirIntegerTypeGet(ctx_, 1);
    MlirValue const operands[]{lhs, rhs};
    MlirOperationState cmp =
        mlirOperationStateGet(mlir_string("arith.cmpi"), loc);
    mlirOperationStateAddOperands(&cmp, 2, operands);
    mlirOperationStateAddResults(&cmp, 1, &i1);
    mlirOperationStateAddAttributes(&cmp, 1, &attr);
    return mlirOperationGetResult(mlir_append(block, &cmp), 0);
}

// (high * 2^64 + low) / divisor, and the remainder, for unsigned 64-bit
// values with high < divisor, so that the quotient fits 64 bits. arith only
// divides values of the same width, and a 128-bit division lowers to a call
// to __udivti3, which IREE's executables can't link. So this is Knuth's
// Algorithm D with 32-bit digits, as Hacker's Delight's divlu: the divisor is
// shifted until its top bit is set, and so is the dividend, so that each
// quotient digit, estimated from the dividend's top digits and the divisor's
// top digit, is at most 2 too large, which two corrections fix. The divisor
// must be nonzero.
//
// In QDiv's kernel, LLVM vectorizes this with AVX-512, turning its 64-bit
// divisions into floating-point reciprocals with corrections, and it runs as
// fast as the interpreter's __divti3, about 4 ns an element
std::pair<MlirValue, MlirValue> Compiler::mlir_divide_narrow(
    MlirLocation const loc, MlirBlock const block, MlirValue const high,
    MlirValue const low, MlirValue const divisor)
{
    MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
    MlirType const i1 = mlirIntegerTypeGet(ctx_, 1);
    auto const constant = [&](int64_t const value) {
        return mlir_constant(loc, block, i64, value);
    };
    auto const arith = [&](std::string_view const name,
                           MlirValue const lhs,
                           MlirValue const rhs) {
        return mlir_value(loc, block, name, {lhs, rhs}, i64);
    };
    auto const select = [&](MlirValue const condition,
                            MlirValue const yes,
                            MlirValue const no) {
        return mlir_value(
            loc, block, "arith.select", {condition, yes, no}, i64);
    };
    int64_t const digit_base = int64_t{1} << 32;
    MlirValue const digit_mask = constant(0xffffffff);

    // Normalized: the divisor's top bit set
    MlirValue const shift = mlir_value(loc, block, "math.ctlz", {divisor}, i64);
    MlirValue const v = arith("arith.shli", divisor, shift);
    // The bits of `low` that shifting `high` moves in. There are none for a
    // shift of 0, for which low >> 64 would be poison
    MlirValue const carried = select(
        mlir_cmpi(loc, block, CMPI_EQ, shift, constant(0)),
        constant(0),
        arith(
            "arith.shrui",
            arith("arith.shrui", low, constant(1)),
            arith("arith.subi", constant(63), shift)));
    MlirValue const u32 =
        arith("arith.ori", arith("arith.shli", high, shift), carried);
    MlirValue const u10 = arith("arith.shli", low, shift);
    MlirValue const v1 = arith("arith.shrui", v, constant(32));
    MlirValue const v0 = arith("arith.andi", v, digit_mask);
    MlirValue const u1 = arith("arith.shrui", u10, constant(32));
    MlirValue const u0 = arith("arith.andi", u10, digit_mask);

    // The quotient digit of dividend * 2^32 + next, for a dividend below
    // v * 2^32: estimated as dividend / v1, which is too large while it's
    // 2^32 or more, or q * v0 > rhat * 2^32 + next. A correction adds v1 to
    // rhat, and once rhat reaches 2^32 the digit is right, as is then the
    // second comparison, whose shift would overflow
    auto const digit = [&](MlirValue const dividend, MlirValue const next) {
        MlirValue q = arith("arith.divui", dividend, v1);
        MlirValue rhat =
            arith("arith.subi", dividend, arith("arith.muli", q, v1));
        auto const too_large = [&] {
            return mlir_value(
                loc,
                block,
                "arith.ori",
                {mlir_cmpi(loc, block, CMPI_UGE, q, constant(digit_base)),
                 mlir_cmpi(
                     loc,
                     block,
                     CMPI_UGT,
                     arith("arith.muli", q, v0),
                     arith(
                         "arith.ori",
                         arith("arith.shli", rhat, constant(32)),
                         next))},
                i1);
        };
        MlirValue const first = too_large();
        q = select(first, arith("arith.subi", q, constant(1)), q);
        rhat = select(first, arith("arith.addi", rhat, v1), rhat);
        MlirValue const second = mlir_value(
            loc,
            block,
            "arith.andi",
            {mlir_value(
                 loc,
                 block,
                 "arith.andi",
                 {first,
                  mlir_cmpi(loc, block, CMPI_ULT, rhat, constant(digit_base))},
                 i1),
             too_large()},
            i1);
        return select(second, arith("arith.subi", q, constant(1)), q);
    };

    MlirValue const q1 = digit(u32, u1);
    // What's left: u32 * 2^32 + u1 - q1 * v, which is below v, so computing
    // it modulo 2^64 is exact
    MlirValue const u21 = arith(
        "arith.subi",
        arith("arith.ori", arith("arith.shli", u32, constant(32)), u1),
        arith("arith.muli", q1, v));
    MlirValue const q0 = digit(u21, u0);
    MlirValue const quotient =
        arith("arith.ori", arith("arith.shli", q1, constant(32)), q0);
    MlirValue const remainder = arith(
        "arith.shrui",
        arith(
            "arith.subi",
            arith("arith.ori", arith("arith.shli", u21, constant(32)), u0),
            arith("arith.muli", q0, v)),
        shift);
    return {quotient, remainder};
}

// floor(sqrt(high * 2^64 + low)), for unsigned 64-bit high and low, with no
// loop, so that IREE can vectorize it. fixed_point.hpp's isqrt uses Newton's
// method from a power of two, but the floor of a square root is unique, so any
// exact method gives its results. Here, for n = high * 2^64 + low and its root
// r:
// 1. A floating-point estimate. n as a double, and its square root, are off by
//    a relative 2^-51 at most, so est = floor(sqrt) is within est / 2^50 + 1
//    of r, and x0 = est + est / 2^50 + 2, capped at 2^64 - 1, is at least r.
//    The square root is first clamped below 2^64, which fptoui can't convert.
// 2. A Newton step from above: x1 = floor((x0 + floor(n / x0)) / 2) is at
//    least r too, and within 1 of it, as x0 is within 2^-49 x0 + 3 of r. The
//    quotient n / x0 reaches 2^64 only when high is x0, since high < sqrt(n),
//    so high <= r <= x0; then its high word is 1, with a remainder of 0.
// 3. Corrections down, while x1^2 > n: one is enough, the second is a margin.
//
// The estimate needs double precision, so IREE_COMPILER_FLAGS keeps IREE from
// demoting f64 to f32. In QInvSqrt's kernel, LLVM vectorizes this but for the
// 128-bit squares, and QInvSqrt runs at about 21 ns an element, against the
// interpreter's 17
MlirValue Compiler::mlir_isqrt(
    MlirLocation const loc, MlirBlock const block, MlirValue const high,
    MlirValue const low)
{
    MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
    MlirType const i128 = mlirIntegerTypeGet(ctx_, 128);
    MlirType const f64 = mlirF64TypeGet(ctx_);
    auto const constant = [&](MlirType const type, __int128 const value) {
        return mlir_constant(loc, block, type, value);
    };
    auto const real = [&](double const value) {
        MlirNamedAttribute const attr =
            mlir_named("value", mlirFloatAttrDoubleGet(ctx_, f64, value));
        MlirOperationState state =
            mlirOperationStateGet(mlir_string("arith.constant"), loc);
        mlirOperationStateAddAttributes(&state, 1, &attr);
        mlirOperationStateAddResults(&state, 1, &f64);
        return mlirOperationGetResult(mlir_append(block, &state), 0);
    };
    auto const unary = [&](std::string_view const name,
                           MlirValue const value,
                           MlirType const type) {
        return mlir_value(loc, block, name, {value}, type);
    };
    auto const arith = [&](std::string_view const name,
                           MlirValue const lhs,
                           MlirValue const rhs) {
        return mlir_value(loc, block, name, {lhs, rhs}, mlirValueGetType(lhs));
    };
    auto const select = [&](MlirValue const condition,
                            MlirValue const yes,
                            MlirValue const no) {
        return mlir_value(
            loc,
            block,
            "arith.select",
            {condition, yes, no},
            mlirValueGetType(yes));
    };
    MlirValue const largest = constant(i64, ~uint64_t{0});

    // 1. The estimate
    MlirValue const n_real = arith(
        "arith.addf",
        arith("arith.mulf", unary("arith.uitofp", high, f64), real(0x1p64)),
        unary("arith.uitofp", low, f64));
    MlirValue const root_real = arith(
        "arith.minimumf",
        unary("math.sqrt", n_real, f64),
        real(0x1.fffffffffffffp63)); // The largest double below 2^64
    MlirValue const estimate = unary("arith.fptoui", root_real, i64);
    MlirValue const margin = arith(
        "arith.addi",
        arith("arith.shrui", estimate, constant(i64, 50)),
        constant(i64, 2));
    MlirValue const x0 = select(
        mlir_cmpi(
            loc,
            block,
            CMPI_UGT,
            estimate,
            arith("arith.subi", largest, margin)),
        largest,
        arith("arith.addi", estimate, margin));

    // 2. The Newton step
    MlirValue const top = mlir_cmpi(loc, block, CMPI_EQ, high, x0);
    MlirValue const quotient_low =
        mlir_divide_narrow(
            loc, block, select(top, constant(i64, 0), high), low, x0)
            .first;
    MlirValue const quotient = arith(
        "arith.ori",
        arith(
            "arith.shli", unary("arith.extui", top, i128), constant(i128, 64)),
        unary("arith.extui", quotient_low, i128));
    MlirValue x1 = arith(
        "arith.shrui",
        arith("arith.addi", unary("arith.extui", x0, i128), quotient),
        constant(i128, 1));
    MlirValue const largest_wide = unary("arith.extui", largest, i128);
    x1 = select(
        mlir_cmpi(loc, block, CMPI_UGT, x1, largest_wide), largest_wide, x1);

    // 3. The corrections
    MlirValue const n = arith(
        "arith.ori",
        arith(
            "arith.shli", unary("arith.extui", high, i128), constant(i128, 64)),
        unary("arith.extui", low, i128));
    for (int i = 0; i < 2; i++) {
        MlirValue const over =
            mlir_cmpi(loc, block, CMPI_UGT, arith("arith.muli", x1, x1), n);
        x1 = select(over, arith("arith.subi", x1, constant(i128, 1)), x1);
    }
    return unary("arith.trunci", x1, i64);
}

// `init` with every element `value`, a scalar of its element type
MlirValue Compiler::mlir_fill(
    MlirLocation const loc, MlirBlock const block, MlirValue const value,
    MlirValue const init)
{
    MlirType const type = mlirValueGetType(init);
    MlirValue const operands[]{value, init};
    std::array<int32_t, 2> const segments{1, 1}; // Inputs, then inits
    MlirNamedAttribute const attr = mlir_named(
        "operandSegmentSizes", mlirDenseI32ArrayGet(ctx_, 2, segments.data()));
    // Named linalg ops are created with an empty region, which
    // mlirLinalgFillBuiltinNamedOpRegion then fills with their body
    MlirRegion const region = mlirRegionCreate();
    MlirOperationState fill =
        mlirOperationStateGet(mlir_string("linalg.fill"), loc);
    mlirOperationStateAddOperands(&fill, 2, operands);
    mlirOperationStateAddResults(&fill, 1, &type);
    mlirOperationStateAddAttributes(&fill, 1, &attr);
    mlirOperationStateAddOwnedRegions(&fill, 1, &region);
    MlirOperation const op = mlir_append(block, &fill);
    mlirLinalgFillBuiltinNamedOpRegion(op);
    return mlirOperationGetResult(op, 0);
}

// A linalg.generic with loops of `iterator_types`, reading `inputs` and
// updating `inits`, whose final values are its results, each operand through
// its indexing map in `maps`, the inputs' then the inits'. `body` appends the
// ops computing the values to yield to the block it's given, from the block's
// arguments, an element of each input then of each init, and returns them
template <typename Body>
MlirOperation Compiler::mlir_generic(
    MlirLocation const loc, MlirBlock const block,
    std::span<MlirValue const> const inputs,
    std::span<MlirValue const> const inits,
    std::span<MlirAttribute const> const maps,
    std::span<MlirAttribute const> const iterator_types, Body const &body)
{
    std::vector<MlirValue> operands{inputs.begin(), inputs.end()};
    operands.insert(operands.end(), inits.begin(), inits.end());
    std::vector<MlirType> element_types;
    element_types.reserve(operands.size());
    for (MlirValue const operand : operands) {
        element_types.push_back(
            mlirShapedTypeGetElementType(mlirValueGetType(operand)));
    }
    std::vector<MlirType> result_types;
    result_types.reserve(inits.size());
    for (MlirValue const init : inits) {
        result_types.push_back(mlirValueGetType(init));
    }
    std::vector<MlirLocation> const locs(operands.size(), loc);

    std::array<int32_t, 2> const segments{
        static_cast<int32_t>(inputs.size()),
        static_cast<int32_t>(inits.size())};
    MlirNamedAttribute const attrs[]{
        mlir_named(
            "indexing_maps",
            mlirArrayAttrGet(
                ctx_, static_cast<intptr_t>(maps.size()), maps.data())),
        mlir_named(
            "iterator_types",
            mlirArrayAttrGet(
                ctx_,
                static_cast<intptr_t>(iterator_types.size()),
                iterator_types.data())),
        mlir_named(
            "operandSegmentSizes",
            mlirDenseI32ArrayGet(ctx_, 2, segments.data())),
    };

    MlirBlock const element = mlirBlockCreate(
        static_cast<intptr_t>(element_types.size()),
        element_types.data(),
        locs.data());
    std::vector<MlirValue> args;
    args.reserve(element_types.size());
    for (size_t i = 0; i < element_types.size(); i++) {
        args.push_back(mlirBlockGetArgument(element, static_cast<intptr_t>(i)));
    }
    std::vector<MlirValue> const yielded =
        body(element, std::span<MlirValue const>{args});
    MlirOperationState yield =
        mlirOperationStateGet(mlir_string("linalg.yield"), loc);
    mlirOperationStateAddOperands(
        &yield, static_cast<intptr_t>(yielded.size()), yielded.data());
    mlir_append(element, &yield);
    MlirRegion const region = mlirRegionCreate();
    mlirRegionAppendOwnedBlock(region, element);

    MlirOperationState generic =
        mlirOperationStateGet(mlir_string("linalg.generic"), loc);
    mlirOperationStateAddOperands(
        &generic, static_cast<intptr_t>(operands.size()), operands.data());
    mlirOperationStateAddResults(
        &generic,
        static_cast<intptr_t>(result_types.size()),
        result_types.data());
    mlirOperationStateAddAttributes(&generic, std::size(attrs), attrs);
    mlirOperationStateAddOwnedRegions(&generic, 1, &region);
    return mlir_append(block, &generic);
}

// A linalg.generic computing the tensor of the next node, values.size(),
// element by element from the tensors of `input_ids`. Their shapes broadcast to
// its shape as numpy's do: each input's dimensions line up with the output's
// last ones, and a dimension of 1 is repeated along a longer counterpart.
// `body` appends the ops computing an element to the block it's given, from
// the block's arguments, an element of each input then the output's, and
// returns the element
template <typename Body>
MlirValue Compiler::mlir_elementwise(
    MlirLocation const loc, MlirBlock const block,
    std::span<size_t const> const input_ids,
    std::vector<MlirValue> const &values, Body const &body)
{
    TensorType const &output = gc_.tensor_types()[values.size()];
    Shape const &output_shape = output.shape();

    // Per input, the indexing map from the loop indices, one per output
    // dimension, to its element
    std::vector<MlirValue> inputs;
    std::vector<MlirAttribute> maps;
    inputs.reserve(input_ids.size());
    maps.reserve(input_ids.size() + 1);
    for (size_t const id : input_ids) {
        Shape const &shape = gc_.tensor_types()[id].shape();
        size_t const offset = output_shape.rank() - shape.rank();
        std::array<MlirAffineExpr, MAX_RANK> exprs{};
        for (size_t i = 0; i < shape.rank(); i++) {
            size_t const dimension = offset + i;
            // Validation checked that the dimensions are equal or this one is
            // 1, and repeating it reads its only element
            exprs[i] =
                shape.dimensions()[i] == output_shape.dimensions()[dimension]
                    ? mlirAffineDimExprGet(
                          ctx_, static_cast<intptr_t>(dimension))
                    : mlirAffineConstantExprGet(ctx_, 0);
        }
        inputs.push_back(values[id]);
        maps.push_back(indexing_map(
            ctx_, output_shape.rank(), {exprs.data(), shape.rank()}));
    }
    maps.push_back(mlirAffineMapAttrGet(
        mlirAffineMapMultiDimIdentityGet(ctx_, output_shape.rank())));
    MlirValue const init = mlir_empty(loc, block, mlir_type(output));
    std::vector<MlirAttribute> const iterator_types(
        output_shape.rank(), iterator_type(ctx_, false));

    MlirOperation const generic = mlir_generic(
        loc,
        block,
        inputs,
        {&init, 1},
        maps,
        iterator_types,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            return std::vector<MlirValue>{body(element, args)};
        });
    return mlirOperationGetResult(generic, 0);
}

// The comparison of two tensors' elements, with `signed_predicate` for signed
// dtypes and `unsigned_predicate` for the others, extended to the output's
// uint8 0 or 1
MlirValue Compiler::mlir_compare(
    MlirLocation const loc, MlirBlock const block,
    std::span<size_t const> const input_ids,
    std::vector<MlirValue> const &values, int64_t const signed_predicate,
    int64_t const unsigned_predicate)
{
    int64_t const predicate =
        is_signed(gc_.tensor_types()[input_ids[0]].dtype())
            ? signed_predicate
            : unsigned_predicate;
    return mlir_elementwise(
        loc,
        block,
        input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            return mlir_value(
                loc,
                element,
                "arith.extui",
                {mlir_cmpi(loc, element, predicate, args[0], args[1])},
                mlirValueGetType(args[2]));
        });
}

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

// TensorRef: the tensor in the account's code, read now, as the interpreter
// reads it when it evaluates the graph, and baked into the module as a
// constant, as a Literal is. InvalidTensorRef if it doesn't match its type.
//
// TODO: the compiled graph is then only valid while the account has the same
// code, so a cache of compiled graphs should be keyed by the code hashes of
// the accounts their TensorRefs read, as well as by their graphcode. An
// account without code can get some through CREATE2, and a contract created
// and self-destructed in one transaction can be recreated with other code
Result<MlirValue> Compiler::mlir_op(
    TensorRefOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &)
{
    auto const &[type, address, offset] = op.params;
    std::vector<uint8_t> data(type.size_bytes());
    Tensor tensor{type, data.data()};
    BOOST_OUTCOME_TRY(load_code_tensor(
        state_, CodeRef{address, offset}, ByteOrder::LittleEndian, tensor));
    auto const value_type = mlir_type(type);
    MlirNamedAttribute const value = mlir_named(
        "value",
        mlir_nonnull(mlirDenseElementsAttrRawBufferGet(
            value_type, data.size(), data.data())));
    MlirOperationState constant =
        mlirOperationStateGet(mlir_string("arith.constant"), loc);
    mlirOperationStateAddAttributes(&constant, 1, &value);
    mlirOperationStateAddResults(&constant, 1, &value_type);
    return mlirOperationGetResult(mlir_append(block, &constant), 0);
}

// arith.addi wraps, as WrappingAdd does
MlirValue Compiler::mlir_op(
    AddOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirOperationState add =
                mlirOperationStateGet(mlir_string("arith.addi"), loc);
            mlirOperationStateAddOperands(&add, 2, args.data());
            mlirOperationStateAddResults(&add, 1, &type);
            return mlirOperationGetResult(mlir_append(element, &add), 0);
        });
}

// arith.subi wraps, as WrappingSub does
MlirValue Compiler::mlir_op(
    SubOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirOperationState sub =
                mlirOperationStateGet(mlir_string("arith.subi"), loc);
            mlirOperationStateAddOperands(&sub, 2, args.data());
            mlirOperationStateAddResults(&sub, 1, &type);
            return mlirOperationGetResult(mlir_append(element, &sub), 0);
        });
}

MlirValue Compiler::mlir_op(
    GreaterOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    return mlir_compare(loc, block, op.input_ids, values, CMPI_SGT, CMPI_UGT);
}

MlirValue Compiler::mlir_op(
    GeOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    return mlir_compare(loc, block, op.input_ids, values, CMPI_SGE, CMPI_UGE);
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

// tensor.reshape, to the output's shape as a constant operand, keeping the
// elements in row-major order
MlirValue Compiler::mlir_op(
    ReshapeOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    TensorType const &type = gc_.tensor_types()[values.size()];
    Shape const &shape = type.shape();
    MlirType const output_type = mlir_type(type);
    std::array<int64_t, MAX_RANK> dimensions{};
    for (size_t i = 0; i < shape.rank(); i++) {
        dimensions[i] = shape.dimensions()[i];
    }
    int64_t const rank = shape.rank();
    MlirType const shape_type = mlirRankedTensorTypeGet(
        1, &rank, mlirIntegerTypeGet(ctx_, 64), mlirAttributeGetNull());
    MlirNamedAttribute const value = mlir_named(
        "value",
        mlir_nonnull(mlirDenseElementsAttrInt64Get(
            shape_type, rank, dimensions.data())));
    MlirOperationState constant =
        mlirOperationStateGet(mlir_string("arith.constant"), loc);
    mlirOperationStateAddAttributes(&constant, 1, &value);
    mlirOperationStateAddResults(&constant, 1, &shape_type);
    MlirValue const operands[]{
        values[op.input_ids[0]],
        mlirOperationGetResult(mlir_append(block, &constant), 0)};

    MlirOperationState reshape =
        mlirOperationStateGet(mlir_string("tensor.reshape"), loc);
    mlirOperationStateAddOperands(&reshape, 2, operands);
    mlirOperationStateAddResults(&reshape, 1, &output_type);
    return mlirOperationGetResult(mlir_append(block, &reshape), 0);
}

// x where the uint8 condition is nonzero, else y
MlirValue Compiler::mlir_op(
    WhereOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    MlirNamedAttribute const predicate = mlir_named(
        "predicate", mlirIntegerAttrGet(mlirIntegerTypeGet(ctx_, 64), CMPI_NE));
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirValue const zero =
                mlir_constant(loc, element, mlirValueGetType(args[0]), 0);
            MlirValue const cmp_operands[]{args[0], zero};
            MlirType const i1 = mlirIntegerTypeGet(ctx_, 1);
            MlirOperationState cmp =
                mlirOperationStateGet(mlir_string("arith.cmpi"), loc);
            mlirOperationStateAddOperands(&cmp, 2, cmp_operands);
            mlirOperationStateAddResults(&cmp, 1, &i1);
            mlirOperationStateAddAttributes(&cmp, 1, &predicate);
            MlirValue const condition =
                mlirOperationGetResult(mlir_append(element, &cmp), 0);

            MlirValue const select_operands[]{condition, args[1], args[2]};
            MlirType const type = mlirValueGetType(args[1]);
            MlirOperationState select =
                mlirOperationStateGet(mlir_string("arith.select"), loc);
            mlirOperationStateAddOperands(&select, 3, select_operands);
            mlirOperationStateAddResults(&select, 1, &type);
            return mlirOperationGetResult(mlir_append(element, &select), 0);
        });
}

// Running sums along the axis, with arith.addi, which wraps as CumSum does:
// out[0] = x[0], then out[i] = out[i - 1] + x[i].
//
// Along an axis of up to MAX_UNROLLED_CUMSUM, the sums are a chain of adds of
// the input's slices along it, joined back together with tensor.concat. Each
// add is elementwise, which IREE vectorizes, while it compiles
// iree_linalg_ext.scan to a scalar loop. The chain has an op per slice, so a
// longer axis uses the scan. Its accumulator, the running sum, which has the
// input's shape without the axis, starts at 0, as a scan split into parts
// carries it between them
MlirValue Compiler::mlir_op(
    CumSumOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    auto const axis = op.params;
    TensorType const &type = gc_.tensor_types()[values.size()];
    Shape const &shape = type.shape();
    MlirType const element_type = mlir_type(type.dtype());
    MlirType const output_type = mlir_type(type);
    MlirValue const input = values[op.input_ids[0]];
    uint64_t const length = shape.dimensions()[axis];

    if (length <= 1) {
        return input; // Its own running sum
    }
    if (length <= MAX_UNROLLED_CUMSUM) {
        // A slice: the input's shape, with 1 along the axis
        std::array<int64_t, MAX_RANK> sizes{};
        for (size_t i = 0; i < shape.rank(); i++) {
            sizes[i] = i == axis ? 1 : shape.dimensions()[i];
        }
        MlirType const slice_type = mlirRankedTensorTypeGet(
            shape.rank(), sizes.data(), element_type, mlirAttributeGetNull());
        std::array<int64_t, MAX_RANK> offsets{};
        std::array<int64_t, MAX_RANK> strides{};
        strides.fill(1);
        // The source, then the dynamic offsets, sizes and strides
        std::array<int32_t, 4> const segments{1, 0, 0, 0};

        std::vector<MlirValue> sums;
        sums.reserve(length);
        for (uint64_t i = 0; i < length; i++) {
            offsets[axis] = static_cast<int64_t>(i);
            MlirNamedAttribute const slice_attrs[]{
                mlir_named(
                    "static_offsets",
                    mlirDenseI64ArrayGet(ctx_, shape.rank(), offsets.data())),
                mlir_named(
                    "static_sizes",
                    mlirDenseI64ArrayGet(ctx_, shape.rank(), sizes.data())),
                mlir_named(
                    "static_strides",
                    mlirDenseI64ArrayGet(ctx_, shape.rank(), strides.data())),
                mlir_named(
                    "operandSegmentSizes",
                    mlirDenseI32ArrayGet(ctx_, 4, segments.data())),
            };
            MlirOperationState extract =
                mlirOperationStateGet(mlir_string("tensor.extract_slice"), loc);
            mlirOperationStateAddOperands(&extract, 1, &input);
            mlirOperationStateAddResults(&extract, 1, &slice_type);
            mlirOperationStateAddAttributes(
                &extract, std::size(slice_attrs), slice_attrs);
            MlirValue const slice =
                mlirOperationGetResult(mlir_append(block, &extract), 0);
            if (sums.empty()) {
                sums.push_back(slice);
                continue;
            }
            MlirValue const addends[]{sums.back(), slice};
            MlirOperationState add =
                mlirOperationStateGet(mlir_string("arith.addi"), loc);
            mlirOperationStateAddOperands(&add, 2, addends);
            mlirOperationStateAddResults(&add, 1, &slice_type);
            sums.push_back(mlirOperationGetResult(mlir_append(block, &add), 0));
        }

        MlirNamedAttribute const dim = mlir_named(
            "dim", mlirIntegerAttrGet(mlirIntegerTypeGet(ctx_, 64), axis));
        MlirOperationState concat =
            mlirOperationStateGet(mlir_string("tensor.concat"), loc);
        mlirOperationStateAddOperands(
            &concat, static_cast<intptr_t>(sums.size()), sums.data());
        mlirOperationStateAddResults(&concat, 1, &output_type);
        mlirOperationStateAddAttributes(&concat, 1, &dim);
        return mlirOperationGetResult(mlir_append(block, &concat), 0);
    }

    std::array<int64_t, MAX_RANK> accumulator_dimensions{};
    intptr_t accumulator_rank = 0;
    for (size_t i = 0; i < shape.rank(); i++) {
        if (i != axis) {
            accumulator_dimensions[static_cast<size_t>(accumulator_rank++)] =
                shape.dimensions()[i];
        }
    }
    MlirType const accumulator_type = mlirRankedTensorTypeGet(
        accumulator_rank,
        accumulator_dimensions.data(),
        element_type,
        mlirAttributeGetNull());

    MlirValue const zero = mlir_constant(loc, block, element_type, 0);
    MlirValue const operands[]{
        input,
        mlir_empty(loc, block, output_type),
        mlir_fill(loc, block, zero, mlir_empty(loc, block, accumulator_type)),
    };
    MlirType const result_types[]{output_type, accumulator_type};
    MlirNamedAttribute const attrs[]{
        mlir_named(
            "dimension",
            mlirIntegerAttrGet(mlirIntegerTypeGet(ctx_, 64), axis)),
        mlir_named("inclusive", mlirBoolAttrGet(ctx_, 1)),
    };

    // The combiner, of the sum so far and the next element
    MlirType const arg_types[]{element_type, element_type};
    MlirLocation const arg_locs[]{loc, loc};
    MlirBlock const combiner = mlirBlockCreate(2, arg_types, arg_locs);
    MlirValue const addends[]{
        mlirBlockGetArgument(combiner, 0), mlirBlockGetArgument(combiner, 1)};
    MlirOperationState add =
        mlirOperationStateGet(mlir_string("arith.addi"), loc);
    mlirOperationStateAddOperands(&add, 2, addends);
    mlirOperationStateAddResults(&add, 1, &element_type);
    MlirValue const sum =
        mlirOperationGetResult(mlir_append(combiner, &add), 0);
    MlirOperationState yield =
        mlirOperationStateGet(mlir_string("iree_linalg_ext.yield"), loc);
    mlirOperationStateAddOperands(&yield, 1, &sum);
    mlir_append(combiner, &yield);
    MlirRegion const region = mlirRegionCreate();
    mlirRegionAppendOwnedBlock(region, combiner);

    MlirOperationState scan =
        mlirOperationStateGet(mlir_string("iree_linalg_ext.scan"), loc);
    mlirOperationStateAddOperands(&scan, std::size(operands), operands);
    mlirOperationStateAddResults(&scan, std::size(result_types), result_types);
    mlirOperationStateAddAttributes(&scan, std::size(attrs), attrs);
    mlirOperationStateAddOwnedRegions(&scan, 1, &region);
    return mlirOperationGetResult(mlir_append(block, &scan), 0);
}

// Converts to the dtype given as the parameter, clamping to its range. Only a
// bound inside the input's range is applied. The clamping is in a signed type
// that holds both dtypes' ranges, its width rounded up to a power of two, from
// which the result is truncated; a conversion that needs no clamping is just
// an extension, by the input's signedness
MlirValue Compiler::mlir_op(
    SaturateOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    Dtype const from = gc_.tensor_types()[op.input_ids[0]].dtype();
    Dtype const to = op.params;
    bool const from_signed = is_signed(from);
    bool const to_signed = is_signed(to);
    unsigned const from_bits = static_cast<unsigned>(8 * dtype_size(from));
    unsigned const to_bits = static_cast<unsigned>(8 * dtype_size(to));
    // A dtype's smallest and largest values
    auto const range = [](unsigned const bits, bool const sign) {
        using i128 = __int128;
        return sign
                   ? std::
                         pair{-(i128{1} << (bits - 1)), (i128{1} << (bits - 1)) - 1}
                   : std::pair{i128{0}, (i128{1} << bits) - 1};
    };
    auto const [from_min, from_max] = range(from_bits, from_signed);
    auto const [to_min, to_max] = range(to_bits, to_signed);
    // A bound that applies is inside the input's range, so it fits an int64:
    // a smallest value is 0 or negative, and a largest value below the
    // input's is below 2^64 - 1
    bool const clamp_min = to_min > from_min;
    bool const clamp_max = to_max < from_max;
    unsigned const wide_bits = std::bit_ceil(std::max(
        from_bits + (from_signed ? 0u : 1u), to_bits + (to_signed ? 0u : 1u)));

    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const to_type = mlirValueGetType(args[1]);
            MlirType const wide_type = clamp_min || clamp_max
                                           ? mlirIntegerTypeGet(ctx_, wide_bits)
                                           : to_type;
            MlirValue value = args[0];
            if (from_bits < mlirIntegerTypeGetWidth(wide_type)) {
                MlirOperationState ext = mlirOperationStateGet(
                    mlir_string(from_signed ? "arith.extsi" : "arith.extui"),
                    loc);
                mlirOperationStateAddOperands(&ext, 1, &value);
                mlirOperationStateAddResults(&ext, 1, &wide_type);
                value = mlirOperationGetResult(mlir_append(element, &ext), 0);
            }
            if (clamp_min) {
                MlirValue const operands[]{
                    value,
                    mlir_constant(
                        loc, element, wide_type, static_cast<int64_t>(to_min))};
                MlirOperationState max =
                    mlirOperationStateGet(mlir_string("arith.maxsi"), loc);
                mlirOperationStateAddOperands(&max, 2, operands);
                mlirOperationStateAddResults(&max, 1, &wide_type);
                value = mlirOperationGetResult(mlir_append(element, &max), 0);
            }
            if (clamp_max) {
                MlirValue const operands[]{
                    value,
                    mlir_constant(
                        loc, element, wide_type, static_cast<int64_t>(to_max))};
                MlirOperationState min =
                    mlirOperationStateGet(mlir_string("arith.minsi"), loc);
                mlirOperationStateAddOperands(&min, 2, operands);
                mlirOperationStateAddResults(&min, 1, &wide_type);
                value = mlirOperationGetResult(mlir_append(element, &min), 0);
            }
            if (!mlirTypeEqual(wide_type, to_type)) {
                MlirOperationState trunc =
                    mlirOperationStateGet(mlir_string("arith.trunci"), loc);
                mlirOperationStateAddOperands(&trunc, 1, &value);
                mlirOperationStateAddResults(&trunc, 1, &to_type);
                value = mlirOperationGetResult(mlir_append(element, &trunc), 0);
            }
            return value;
        });
}

// linalg.matmul accumulates into its init operand, here zeros, and
// sign-extends the int8 elements to the int32 output's type before multiplying
MlirValue Compiler::mlir_op(
    MatMulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    TensorType const &type = gc_.tensor_types()[values.size()];
    MlirType const output_type = mlir_type(type);
    MlirValue const zero =
        mlir_constant(loc, block, mlir_type(type.dtype()), 0);
    if (gc_.tensor_types()[op.input_ids[0]].shape().dimensions()[1] == 0) {
        // No products, so every element is 0. IREE can't compile an empty
        // reduction: see compile()
        return mlir_fill(loc, block, zero, mlir_empty(loc, block, output_type));
    }
    MlirValue const operands[]{
        values[op.input_ids[0]],
        values[op.input_ids[1]],
        mlir_fill(loc, block, zero, mlir_empty(loc, block, output_type)),
    };
    std::array<int32_t, 2> const segments{2, 1}; // Inputs, then inits
    MlirNamedAttribute const attr = mlir_named(
        "operandSegmentSizes", mlirDenseI32ArrayGet(ctx_, 2, segments.data()));
    // Named linalg ops are created with an empty region, which
    // mlirLinalgFillBuiltinNamedOpRegion then fills with their body
    MlirRegion const region = mlirRegionCreate();
    MlirOperationState matmul =
        mlirOperationStateGet(mlir_string("linalg.matmul"), loc);
    mlirOperationStateAddOperands(&matmul, std::size(operands), operands);
    mlirOperationStateAddResults(&matmul, 1, &output_type);
    mlirOperationStateAddAttributes(&matmul, 1, &attr);
    mlirOperationStateAddOwnedRegions(&matmul, 1, &region);
    MlirOperation const matmul_op = mlir_append(block, &matmul);
    mlirLinalgFillBuiltinNamedOpRegion(matmul_op);
    return mlirOperationGetResult(matmul_op, 0);
}

// One linalg.generic reducing over every dimension, which carries the largest
// element so far and its row-major index. An element replaces them only if
// it's strictly larger, so the first of equal ones stays; they start as the
// dtype's smallest value and 0, which is right even if every element is that
// value. The index, an int64, is then truncated to the input's dtype, so it
// wraps as ArgMax's does.
//
// TODO: check that ties still go to the first index when IREE splits this
// reduction. Its SplitReduction pass recognizes argmax generics
// (IREE::LinalgExt::isArgmaxOp) and splits those whose reduction is at least
// --iree-dispatch-creation-split-argmax-threshold (128 * 1024 by default)
MlirValue Compiler::mlir_op(
    ArgMaxOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    TensorType const &input = gc_.tensor_types()[op.input_ids[0]];
    Shape const &shape = input.shape();
    intptr_t const rank = shape.rank();
    bool const sign = is_signed(input.dtype());
    MlirType const element_type = mlir_type(input.dtype());
    MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
    MlirType const index = mlirIndexTypeGet(ctx_);
    MlirType const value_type = mlirRankedTensorTypeGet(
        0, nullptr, element_type, mlirAttributeGetNull());
    MlirType const index_type =
        mlirRankedTensorTypeGet(0, nullptr, i64, mlirAttributeGetNull());

    int64_t const smallest =
        sign ? -(int64_t{1} << (8 * dtype_size(input.dtype()) - 1)) : 0;
    MlirValue const inits[]{
        mlir_fill(
            loc,
            block,
            mlir_constant(loc, block, element_type, smallest),
            mlir_empty(loc, block, value_type)),
        mlir_fill(
            loc,
            block,
            mlir_constant(loc, block, i64, 0),
            mlir_empty(loc, block, index_type)),
    };

    // The input's element per iteration, and the two scalars for every one
    MlirAttribute const scalar = indexing_map(ctx_, shape.rank(), {});
    MlirAttribute const maps[]{
        mlirAffineMapAttrGet(mlirAffineMapMultiDimIdentityGet(ctx_, rank)),
        scalar,
        scalar,
    };
    std::vector<MlirAttribute> const iterator_types(
        static_cast<size_t>(rank), iterator_type(ctx_, true));

    // The body: the element, then the largest so far and its index
    MlirOperation const generic = mlir_generic(
        loc,
        block,
        {&values[op.input_ids[0]], 1},
        inits,
        maps,
        iterator_types,
        [&](MlirBlock const body, std::span<MlirValue const> const args) {
            MlirValue const element = args[0];
            MlirValue const largest = args[1];
            MlirValue const largest_index = args[2];

            // The element's row-major index, from linalg.index's loop indices
            MlirValue position = mlir_constant(loc, body, index, 0);
            for (intptr_t i = 0; i < rank; i++) {
                MlirNamedAttribute const dim =
                    mlir_named("dim", mlirIntegerAttrGet(i64, i));
                MlirOperationState loop_index =
                    mlirOperationStateGet(mlir_string("linalg.index"), loc);
                mlirOperationStateAddAttributes(&loop_index, 1, &dim);
                mlirOperationStateAddResults(&loop_index, 1, &index);
                MlirValue const scaled = mlir_value(
                    loc,
                    body,
                    "arith.muli",
                    {position,
                     mlir_constant(
                         loc,
                         body,
                         index,
                         shape.dimensions()[static_cast<size_t>(i)])},
                    index);
                position = mlir_value(
                    loc,
                    body,
                    "arith.addi",
                    {scaled,
                     mlirOperationGetResult(mlir_append(body, &loop_index), 0)},
                    index);
            }
            MlirValue const element_index =
                mlir_value(loc, body, "arith.index_cast", {position}, i64);

            MlirValue const larger = mlir_cmpi(
                loc, body, sign ? CMPI_SGT : CMPI_UGT, element, largest);
            return std::vector<MlirValue>{
                mlir_value(
                    loc,
                    body,
                    "arith.select",
                    {larger, element, largest},
                    element_type),
                mlir_value(
                    loc,
                    body,
                    "arith.select",
                    {larger, element_index, largest_index},
                    i64)};
        });
    MlirValue result = mlirOperationGetResult(generic, 1);

    // The index in the input's dtype
    if (!mlirTypeEqual(element_type, i64)) {
        result = mlir_value(
            loc,
            block,
            "arith.trunci",
            {result},
            mlir_type(gc_.tensor_types()[values.size()]));
    }
    return result;
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

// The larger element, by the inputs' signedness
MlirValue Compiler::mlir_op(
    MaxOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    std::string_view const name =
        is_signed(gc_.tensor_types()[op.input_ids[0]].dtype()) ? "arith.maxsi"
                                                               : "arith.maxui";
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirOperationState extremum =
                mlirOperationStateGet(mlir_string(name), loc);
            mlirOperationStateAddOperands(&extremum, 2, args.data());
            mlirOperationStateAddResults(&extremum, 1, &type);
            return mlirOperationGetResult(mlir_append(element, &extremum), 0);
        });
}

// The smaller element, by the inputs' signedness
MlirValue Compiler::mlir_op(
    MinOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    std::string_view const name =
        is_signed(gc_.tensor_types()[op.input_ids[0]].dtype()) ? "arith.minsi"
                                                               : "arith.minui";
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirOperationState extremum =
                mlirOperationStateGet(mlir_string(name), loc);
            mlirOperationStateAddOperands(&extremum, 2, args.data());
            mlirOperationStateAddResults(&extremum, 1, &type);
            return mlirOperationGetResult(mlir_append(element, &extremum), 0);
        });
}

// The product in the output's type, which is twice as wide as the inputs' but
// for 64-bit inputs, after extending them by their signedness. arith.muli
// wraps, which only 64-bit products can, as WideningMul's do
MlirValue Compiler::mlir_op(
    MulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    std::string_view const extend =
        is_signed(gc_.tensor_types()[op.input_ids[0]].dtype()) ? "arith.extsi"
                                                               : "arith.extui";
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[2]);
            std::array<MlirValue, 2> factors{args[0], args[1]};
            for (MlirValue &factor : factors) {
                if (mlirTypeEqual(mlirValueGetType(factor), type)) {
                    continue;
                }
                MlirOperationState ext =
                    mlirOperationStateGet(mlir_string(extend), loc);
                mlirOperationStateAddOperands(&ext, 1, &factor);
                mlirOperationStateAddResults(&ext, 1, &type);
                factor = mlirOperationGetResult(mlir_append(element, &ext), 0);
            }
            MlirOperationState mul =
                mlirOperationStateGet(mlir_string("arith.muli"), loc);
            mlirOperationStateAddOperands(&mul, 2, factors.data());
            mlirOperationStateAddResults(&mul, 1, &type);
            return mlirOperationGetResult(mlir_append(element, &mul), 0);
        });
}

// x / denominator, truncated toward zero, as DivOp computes it: in int64 for
// every dtype but uint64, whose quotient by the denominator's magnitude is
// negated, wrapping, for a negative denominator. Dividing by -1 is a negation,
// which wraps for int64's smallest value, where arith.divsi's result is
// undefined. Validation rejected a zero denominator
MlirValue Compiler::mlir_op(
    DivOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    int64_t const denominator = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
            // The negation of a 64-bit value
            auto const negate = [&](MlirValue const value) {
                MlirValue const operands[]{
                    mlir_constant(loc, element, i64, 0), value};
                MlirOperationState sub =
                    mlirOperationStateGet(mlir_string("arith.subi"), loc);
                mlirOperationStateAddOperands(&sub, 2, operands);
                mlirOperationStateAddResults(&sub, 1, &i64);
                return mlirOperationGetResult(mlir_append(element, &sub), 0);
            };

            if (dtype == Dtype::uint64) {
                uint64_t const magnitude =
                    denominator < 0
                        ? uint64_t{0} - static_cast<uint64_t>(denominator)
                        : static_cast<uint64_t>(denominator);
                MlirValue const operands[]{
                    args[0],
                    mlir_constant(
                        loc, element, i64, static_cast<int64_t>(magnitude))};
                MlirOperationState div =
                    mlirOperationStateGet(mlir_string("arith.divui"), loc);
                mlirOperationStateAddOperands(&div, 2, operands);
                mlirOperationStateAddResults(&div, 1, &i64);
                MlirValue const quotient =
                    mlirOperationGetResult(mlir_append(element, &div), 0);
                return denominator < 0 ? negate(quotient) : quotient;
            }

            MlirValue x = args[0];
            if (!mlirTypeEqual(type, i64)) {
                MlirOperationState ext = mlirOperationStateGet(
                    mlir_string(
                        is_signed(dtype) ? "arith.extsi" : "arith.extui"),
                    loc);
                mlirOperationStateAddOperands(&ext, 1, &x);
                mlirOperationStateAddResults(&ext, 1, &i64);
                x = mlirOperationGetResult(mlir_append(element, &ext), 0);
            }
            MlirValue quotient;
            if (denominator == -1) {
                quotient = negate(x);
            }
            else {
                MlirValue const operands[]{
                    x, mlir_constant(loc, element, i64, denominator)};
                MlirOperationState div =
                    mlirOperationStateGet(mlir_string("arith.divsi"), loc);
                mlirOperationStateAddOperands(&div, 2, operands);
                mlirOperationStateAddResults(&div, 1, &i64);
                quotient =
                    mlirOperationGetResult(mlir_append(element, &div), 0);
            }
            if (mlirTypeEqual(type, i64)) {
                return quotient;
            }
            MlirOperationState trunc =
                mlirOperationStateGet(mlir_string("arith.trunci"), loc);
            mlirOperationStateAddOperands(&trunc, 1, &quotient);
            mlirOperationStateAddResults(&trunc, 1, &type);
            return mlirOperationGetResult(mlir_append(element, &trunc), 0);
        });
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

// The input, broadcast to the shape, as mlir_elementwise broadcasts its inputs
MlirValue Compiler::mlir_op(
    ExpandOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [](MlirBlock, std::span<MlirValue const> const args) {
            return args[0];
        });
}

// q_mul: floor(a * b / 2^bits), wrapping to the dtype, as fixed_point.hpp
// computes it: the product of the inputs extended by their signedness, exact
// in 64 bits for dtypes up to 32 bits wide and in 128 bits otherwise, then
// shifted, arithmetically for a signed dtype, and truncated
MlirValue Compiler::mlir_op(
    QMulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    unsigned const bits = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = is_signed(dtype);
    MlirType const wide =
        mlirIntegerTypeGet(ctx_, dtype_size(dtype) <= 4 ? 64 : 128);
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            auto const extend = [&](MlirValue const value) {
                return mlir_value(
                    loc,
                    element,
                    sign ? "arith.extsi" : "arith.extui",
                    {value},
                    wide);
            };
            MlirValue const product = mlir_value(
                loc,
                element,
                "arith.muli",
                {extend(args[0]), extend(args[1])},
                wide);
            MlirValue const shifted = mlir_value(
                loc,
                element,
                sign ? "arith.shrsi" : "arith.shrui",
                {product, mlir_constant(loc, element, wide, bits)},
                wide);
            return mlir_value(
                loc,
                element,
                "arith.trunci",
                {shifted},
                mlirValueGetType(args[0]));
        });
}

// q_div: a * 2^bits / b, truncated toward zero and wrapping to the dtype. In
// fixed_point.hpp that's a 128-bit division; here it's a long division of the
// magnitudes in 64-bit words. The dividend |a| * 2^bits has a high and a low
// word, and the wrapping keeps only the quotient's low word, which is
// (high % |b|, low) / |b|, a division whose quotient fits 64 bits, as
// mlir_divide_narrow does. The result is negated if the signs differ.
//
// TODO: report a zero divisor, a DivisionByZero for the interpreter. Here it's
// replaced by 1, so that dividing by it can't trap, and the element is wrong
MlirValue Compiler::mlir_op(
    QDivOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    unsigned const bits = op.params;
    bool const sign = is_signed(gc_.tensor_types()[op.input_ids[0]].dtype());
    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
            MlirType const i1 = mlirIntegerTypeGet(ctx_, 1);
            auto const constant = [&](int64_t const value) {
                return mlir_constant(loc, element, i64, value);
            };
            auto const arith = [&](std::string_view const name,
                                   MlirValue const lhs,
                                   MlirValue const rhs) {
                return mlir_value(loc, element, name, {lhs, rhs}, i64);
            };
            auto const select = [&](MlirValue const condition,
                                    MlirValue const yes,
                                    MlirValue const no) {
                return mlir_value(
                    loc, element, "arith.select", {condition, yes, no}, i64);
            };
            auto const widen = [&](MlirValue const value) {
                return mlirTypeEqual(type, i64)
                           ? value
                           : mlir_value(
                                 loc,
                                 element,
                                 sign ? "arith.extsi" : "arith.extui",
                                 {value},
                                 i64);
            };
            auto const negative = [&](MlirValue const value) {
                return mlir_cmpi(loc, element, CMPI_SLT, value, constant(0));
            };
            // As unsigned: |INT64_MIN| is 2^63
            auto const magnitude = [&](MlirValue const value) {
                return sign ? select(
                                  negative(value),
                                  arith("arith.subi", constant(0), value),
                                  value)
                            : value;
            };

            MlirValue const a = widen(args[0]);
            MlirValue const b = widen(args[1]);
            MlirValue const b_magnitude = magnitude(b);
            MlirValue const divisor = select(
                mlir_cmpi(loc, element, CMPI_EQ, b_magnitude, constant(0)),
                constant(1),
                b_magnitude);
            MlirValue const a_magnitude = magnitude(a);
            MlirValue const high =
                bits == 0
                    ? constant(0)
                    : arith("arith.shrui", a_magnitude, constant(64 - bits));
            MlirValue const low =
                arith("arith.shli", a_magnitude, constant(bits));
            MlirValue quotient = mlir_divide_narrow(
                                     loc,
                                     element,
                                     arith("arith.remui", high, divisor),
                                     low,
                                     divisor)
                                     .first;
            if (sign) {
                MlirValue const signs_differ = mlir_value(
                    loc, element, "arith.xori", {negative(a), negative(b)}, i1);
                quotient = select(
                    signs_differ,
                    arith("arith.subi", constant(0), quotient),
                    quotient);
            }
            return mlirTypeEqual(type, i64)
                       ? quotient
                       : mlir_value(
                             loc, element, "arith.trunci", {quotient}, type);
        });
}

// q_matmul, as matmul.cpp's matmul_generic computes it: each element is the
// sum of its products, of the inputs extended by their signedness, exact and
// wrapping at 128 bits, then shifted right by `bits`, arithmetically for a
// signed dtype, and truncated to the output's dtype. The sums are computed in
// 64 bits, wrapping, where that gives the same result, as matmul() chooses
// them: for dtypes up to 16 bits wide, whose sums are exact in 64 bits, and
// when only bits below 64 of a sum reach the output, from `bits` to `bits`
// plus its width; otherwise in 128. arith.muli and arith.addi wrap, so a
// 64-bit product of 64-bit inputs is its low 64 bits. A linalg.generic sums
// the products, over the loops (i, j, k) of out[i, j] += x[i, k] * y[k, j],
// and an elementwise one shifts and truncates.
//
// TODO: speed up the 128-bit sums. IREE vectorizes them, and LLVM, as x86
// has no vector 64 x 64 -> 128-bit multiply, takes the vectors apart again:
// in stories.graph they take about 0.62 ns a product, against about 0.44 ns
// in the interpreter's scalar loop. Keeping the loop scalar should at least
// match the interpreter, and see matmul.cpp's matmul_generic for what may be
// left beyond it
MlirValue Compiler::mlir_op(
    QMatMulOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    auto const [bits, out_dtype] = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = is_signed(dtype);
    TensorType const &output = gc_.tensor_types()[values.size()];
    bool const short_sums =
        dtype_size(dtype) <= 2 || bits + 8 * dtype_size(out_dtype) <= 64;
    unsigned const wide_bits = short_sums ? 64 : 128;
    MlirType const wide = mlirIntegerTypeGet(ctx_, wide_bits);
    std::array<int64_t, 2> const dimensions{
        output.shape().dimensions()[0], output.shape().dimensions()[1]};
    MlirType const sums_type = mlirRankedTensorTypeGet(
        2, dimensions.data(), wide, mlirAttributeGetNull());
    if (gc_.tensor_types()[op.input_ids[0]].shape().dimensions()[1] == 0) {
        // No products, so every sum is 0, and so is every element. IREE can't
        // compile an empty reduction: see compile()
        return mlir_fill(
            loc,
            block,
            mlir_constant(loc, block, mlir_type(out_dtype), 0),
            mlir_empty(loc, block, mlir_type(output)));
    }
    MlirValue const zeros = mlir_fill(
        loc,
        block,
        mlir_constant(loc, block, wide, 0),
        mlir_empty(loc, block, sums_type));

    std::array<MlirAffineExpr, 3> const loops{
        mlirAffineDimExprGet(ctx_, 0),
        mlirAffineDimExprGet(ctx_, 1),
        mlirAffineDimExprGet(ctx_, 2)};
    std::array<MlirAffineExpr, 2> x_exprs{loops[0], loops[2]};
    std::array<MlirAffineExpr, 2> y_exprs{loops[2], loops[1]};
    std::array<MlirAffineExpr, 2> out_exprs{loops[0], loops[1]};
    MlirAttribute const maps[]{
        indexing_map(ctx_, 3, x_exprs),
        indexing_map(ctx_, 3, y_exprs),
        indexing_map(ctx_, 3, out_exprs),
    };
    MlirAttribute const parallel = iterator_type(ctx_, false);
    MlirAttribute const iterator_types[]{
        parallel, parallel, iterator_type(ctx_, true)};
    MlirValue const inputs[]{values[op.input_ids[0]], values[op.input_ids[1]]};
    MlirOperation const sums = mlir_generic(
        loc,
        block,
        inputs,
        {&zeros, 1},
        maps,
        iterator_types,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            auto const extend = [&](MlirValue const value) {
                return 8 * dtype_size(dtype) == wide_bits
                           ? value
                           : mlir_value(
                                 loc,
                                 element,
                                 sign ? "arith.extsi" : "arith.extui",
                                 {value},
                                 wide);
            };
            MlirValue const product = mlir_value(
                loc,
                element,
                "arith.muli",
                {extend(args[0]), extend(args[1])},
                wide);
            return std::vector<MlirValue>{mlir_value(
                loc, element, "arith.addi", {args[2], product}, wide)};
        });

    MlirValue const sums_value = mlirOperationGetResult(sums, 0);
    MlirValue const init = mlir_empty(loc, block, mlir_type(output));
    MlirAttribute const identity =
        mlirAffineMapAttrGet(mlirAffineMapMultiDimIdentityGet(ctx_, 2));
    MlirAttribute const shift_maps[]{identity, identity};
    MlirAttribute const shift_iterator_types[]{parallel, parallel};
    MlirOperation const shifted = mlir_generic(
        loc,
        block,
        {&sums_value, 1},
        {&init, 1},
        shift_maps,
        shift_iterator_types,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirValue value = mlir_value(
                loc,
                element,
                sign ? "arith.shrsi" : "arith.shrui",
                {args[0], mlir_constant(loc, element, wide, bits)},
                wide);
            MlirType const out_type = mlir_type(out_dtype);
            if (!mlirTypeEqual(out_type, wide)) {
                value =
                    mlir_value(loc, element, "arith.trunci", {value}, out_type);
            }
            return std::vector<MlirValue>{value};
        });
    return mlirOperationGetResult(shifted, 0);
}

// The input's elements combined along the axis with `combine`, an arith op,
// starting from `initial`: a linalg.generic reducing the axis away, from a
// tensor of `initial`, so that an empty axis gives `initial`, then
// tensor.expand_shape putting the axis back, with length 1
MlirValue Compiler::mlir_reduce(
    MlirLocation const loc, MlirBlock const block, size_t const axis,
    size_t const input_id, std::vector<MlirValue> const &values,
    std::string_view const combine, __int128 const initial)
{
    TensorType const &input = gc_.tensor_types()[input_id];
    Shape const &shape = input.shape();
    size_t const rank = shape.rank();
    MlirType const element_type = mlir_type(input.dtype());
    TensorType const &output = gc_.tensor_types()[values.size()];
    MlirType const output_type = mlir_type(output);
    MlirValue const start = mlir_constant(loc, block, element_type, initial);
    if (shape.dimensions()[axis] == 0) {
        // Nothing to reduce, which IREE can't compile: see compile()
        return mlir_fill(
            loc, block, start, mlir_empty(loc, block, output_type));
    }

    // The loops are the input's dimensions, of which the reduced tensor has
    // all but the axis
    std::array<MlirAffineExpr, MAX_RANK> input_exprs{};
    std::array<MlirAffineExpr, MAX_RANK> reduced_exprs{};
    std::array<int64_t, MAX_RANK> reduced_dimensions{};
    std::vector<MlirAttribute> iterator_types;
    size_t reduced_rank = 0;
    for (size_t i = 0; i < rank; i++) {
        input_exprs[i] = mlirAffineDimExprGet(ctx_, static_cast<intptr_t>(i));
        iterator_types.push_back(iterator_type(ctx_, i == axis));
        if (i != axis) {
            reduced_exprs[reduced_rank] = input_exprs[i];
            reduced_dimensions[reduced_rank] = shape.dimensions()[i];
            reduced_rank++;
        }
    }
    MlirType const reduced_type = mlirRankedTensorTypeGet(
        static_cast<intptr_t>(reduced_rank),
        reduced_dimensions.data(),
        element_type,
        mlirAttributeGetNull());
    MlirValue const init =
        mlir_fill(loc, block, start, mlir_empty(loc, block, reduced_type));
    MlirAttribute const maps[]{
        indexing_map(ctx_, rank, {input_exprs.data(), rank}),
        indexing_map(ctx_, rank, {reduced_exprs.data(), reduced_rank}),
    };
    MlirOperation const reduce = mlir_generic(
        loc,
        block,
        {&values[input_id], 1},
        {&init, 1},
        maps,
        iterator_types,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            return std::vector<MlirValue>{mlir_value(
                loc, element, combine, {args[1], args[0]}, element_type)};
        });

    // Each of the reduced tensor's dimensions expands to its own in the
    // output, and the axis to the one before it, or after it for axis 0
    std::vector<std::vector<int64_t>> groups;
    for (size_t i = 0; i < rank; i++) {
        if (i != axis) {
            groups.push_back({static_cast<int64_t>(i)});
        }
    }
    if (axis > 0) {
        groups[axis - 1].push_back(static_cast<int64_t>(axis));
    }
    else if (!groups.empty()) {
        groups.front().insert(groups.front().begin(), 0);
    }
    MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
    std::vector<MlirAttribute> reassociation;
    for (auto const &group : groups) {
        std::vector<MlirAttribute> indices;
        for (int64_t const i : group) {
            indices.push_back(mlirIntegerAttrGet(i64, i));
        }
        reassociation.push_back(mlirArrayAttrGet(
            ctx_, static_cast<intptr_t>(indices.size()), indices.data()));
    }
    std::array<int64_t, MAX_RANK> dimensions{};
    for (size_t i = 0; i < rank; i++) {
        dimensions[i] = output.shape().dimensions()[i];
    }
    MlirNamedAttribute const attrs[]{
        mlir_named(
            "reassociation",
            mlirArrayAttrGet(
                ctx_,
                static_cast<intptr_t>(reassociation.size()),
                reassociation.data())),
        mlir_named(
            "static_output_shape",
            mlirDenseI64ArrayGet(
                ctx_, static_cast<intptr_t>(rank), dimensions.data())),
    };
    MlirValue const reduced = mlirOperationGetResult(reduce, 0);
    MlirOperationState expand =
        mlirOperationStateGet(mlir_string("tensor.expand_shape"), loc);
    mlirOperationStateAddOperands(&expand, 1, &reduced);
    mlirOperationStateAddResults(&expand, 1, &output_type);
    mlirOperationStateAddAttributes(&expand, std::size(attrs), attrs);
    return mlirOperationGetResult(mlir_append(block, &expand), 0);
}

// arith.addi wraps, as WrappingAdd does
MlirValue Compiler::mlir_op(
    ReduceSumOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    return mlir_reduce(
        loc, block, op.params, op.input_ids[0], values, "arith.addi", 0);
}

// Validation rejected an empty axis, so the dtype's smallest value, the start,
// is never the result unless it's an element
MlirValue Compiler::mlir_op(
    ReduceMaxOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = is_signed(dtype);
    __int128 const smallest =
        sign ? -(__int128{1} << (8 * dtype_size(dtype) - 1)) : 0;
    return mlir_reduce(
        loc,
        block,
        op.params,
        op.input_ids[0],
        values,
        sign ? "arith.maxsi" : "arith.maxui",
        smallest);
}

// q_exp: e^(x / 2^bits), rounded down and saturating, as fixed_point.hpp
// computes it: x / ln 2 is split into an integer k and a remainder r, e^r is
// a polynomial, and the result is that times 2^k. fixed_point.hpp divides by
// ln 2 in 128 bits; here k is estimated by multiplying by a reciprocal of
// ln 2 instead. The estimate is off by less than 1, below for a nonnegative
// dividend and above for a negative one, so a correction either way gives
// the same k and r
MlirValue Compiler::mlir_op(
    QExpOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    unsigned const bits = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = is_signed(dtype);
    unsigned const width = static_cast<unsigned>(8 * dtype_size(dtype));
    uint64_t const largest =
        sign ? (uint64_t{1} << (width - 1)) - 1 : ~uint64_t{0} >> (64 - width);
    // floor(2^120 / ln 2), where ln 2 is LN2_Q64 / 2^64: below 2^57, and the
    // dividend is below 45 * 2^64, so their product fits an int128
    constexpr unsigned RECIPROCAL_SHIFT = 120;
    constexpr __int128 RECIPROCAL = static_cast<__int128>(
        (static_cast<unsigned __int128>(1) << RECIPROCAL_SHIFT) / LN2_Q64);
    __int128 const limit = static_cast<__int128>(EXP_LIMIT) << bits;

    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
            MlirType const i128 = mlirIntegerTypeGet(ctx_, 128);
            MlirType const i1 = mlirIntegerTypeGet(ctx_, 1);
            auto const constant = [&](MlirType const t, __int128 const value) {
                return mlir_constant(loc, element, t, value);
            };
            auto const arith = [&](std::string_view const name,
                                   MlirValue const lhs,
                                   MlirValue const rhs) {
                return mlir_value(
                    loc, element, name, {lhs, rhs}, mlirValueGetType(lhs));
            };
            auto const select = [&](MlirValue const condition,
                                    MlirValue const yes,
                                    MlirValue const no) {
                return mlir_value(
                    loc,
                    element,
                    "arith.select",
                    {condition, yes, no},
                    mlirValueGetType(yes));
            };
            auto const cmp = [&](int64_t const predicate,
                                 MlirValue const lhs,
                                 MlirValue const rhs) {
                return mlir_cmpi(loc, element, predicate, lhs, rhs);
            };

            MlirValue const value = mlir_value(
                loc,
                element,
                sign ? "arith.extsi" : "arith.extui",
                {args[0]},
                i128);
            MlirValue const v =
                arith("arith.shli", value, constant(i128, 64 - bits));
            MlirValue const ln2 =
                constant(i128, static_cast<__int128>(LN2_Q64));

            // k = floor(v / ln 2), and r = v - k ln 2, in [0, ln 2)
            MlirValue k = arith(
                "arith.shrsi",
                arith("arith.muli", v, constant(i128, RECIPROCAL)),
                constant(i128, RECIPROCAL_SHIFT));
            MlirValue r = arith("arith.subi", v, arith("arith.muli", k, ln2));
            MlirValue const below = cmp(CMPI_SLT, r, constant(i128, 0));
            k = select(below, arith("arith.subi", k, constant(i128, 1)), k);
            r = select(below, arith("arith.addi", r, ln2), r);
            MlirValue const above = cmp(CMPI_SGE, r, ln2);
            k = select(above, arith("arith.addi", k, constant(i128, 1)), k);
            r = select(above, arith("arith.subi", r, ln2), r);

            // e^r, with 64 fractional bits, by Horner's rule
            MlirValue const r63 = mlir_value(
                loc,
                element,
                "arith.trunci",
                {arith("arith.shrui", r, constant(i128, 1))},
                i64);
            MlirValue const r63_wide =
                mlir_value(loc, element, "arith.extui", {r63}, i128);
            MlirValue p = constant(
                i64, static_cast<__int128>(EXP_COEFFICIENTS[EXP_TERMS - 1]));
            for (size_t n = EXP_TERMS - 1; n-- > 0;) {
                MlirValue const product = arith(
                    "arith.muli",
                    mlir_value(loc, element, "arith.extui", {p}, i128),
                    r63_wide);
                p = arith(
                    "arith.addi",
                    constant(i64, static_cast<__int128>(EXP_COEFFICIENTS[n])),
                    mlir_value(
                        loc,
                        element,
                        "arith.trunci",
                        {arith("arith.shrui", product, constant(i128, 63))},
                        i64));
            }

            // p * 2^shift: past the dtype for a positive shift, and 0 for one
            // of -64 or below
            MlirValue const shift = arith(
                "arith.addi",
                mlir_value(loc, element, "arith.trunci", {k}, i64),
                constant(i64, static_cast<__int128>(bits) - 63));
            MlirValue const in_range = mlir_value(
                loc,
                element,
                "arith.andi",
                {cmp(CMPI_SLE, shift, constant(i64, 0)),
                 cmp(CMPI_SGT, shift, constant(i64, -64))},
                i1);
            MlirValue const shifted = arith(
                "arith.shrui",
                p,
                select(
                    in_range,
                    arith("arith.subi", constant(i64, 0), shift),
                    constant(i64, 0)));
            MlirValue const max = constant(i64, static_cast<__int128>(largest));
            MlirValue result =
                select(cmp(CMPI_UGT, shifted, max), max, shifted);
            result = select(
                cmp(CMPI_SLE, shift, constant(i64, -64)),
                constant(i64, 0),
                result);
            result =
                select(cmp(CMPI_SGT, shift, constant(i64, 0)), max, result);
            // Past the limits, p's terms aren't enough: saturate
            result = select(
                cmp(CMPI_SLE, value, constant(i128, -limit)),
                constant(i64, 0),
                result);
            result = select(
                cmp(CMPI_SGE, value, constant(i128, limit)), max, result);
            return mlirTypeEqual(type, i64)
                       ? result
                       : mlir_value(
                             loc, element, "arith.trunci", {result}, type);
        });
}

// q_inv_sqrt: floor(sqrt(2^(3 bits) / x)), saturating at the dtype's largest
// value, for a positive x, as fixed_point.hpp computes it. 2^(3 bits) / x is a
// long division of the 64-bit words of 2^(3 bits), from the top, by x, each
// step one mlir_divide_narrow. From 3 bits = 128 on, the quotient can pass
// 128 bits, which happens exactly when x <= 2^(3 bits - 128), and saturates;
// otherwise its top word is 0. The root is then mlir_isqrt's.
//
// TODO: report an x that isn't positive: a DivisionByZero for 0 and a
// DomainError for a negative x for the interpreter. Here it's replaced by 1,
// so that dividing by it can't trap, and the element is wrong
MlirValue Compiler::mlir_op(
    QInvSqrtOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    unsigned const exponent = 3u * op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = is_signed(dtype);
    unsigned const width = static_cast<unsigned>(8 * dtype_size(dtype));
    uint64_t const largest =
        sign ? (uint64_t{1} << (width - 1)) - 1 : ~uint64_t{0} >> (64 - width);
    // 2^exponent's words, from the top
    std::vector<uint64_t> words(exponent / 64 + 1, 0);
    words.front() = uint64_t{1} << (exponent % 64);

    return mlir_elementwise(
        loc,
        block,
        op.input_ids,
        values,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const type = mlirValueGetType(args[0]);
            MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
            auto const constant = [&](uint64_t const value) {
                return mlir_constant(
                    loc, element, i64, static_cast<__int128>(value));
            };
            auto const select = [&](MlirValue const condition,
                                    MlirValue const yes,
                                    MlirValue const no) {
                return mlir_value(
                    loc, element, "arith.select", {condition, yes, no}, i64);
            };

            MlirValue const x = mlirTypeEqual(type, i64)
                                    ? args[0]
                                    : mlir_value(
                                          loc,
                                          element,
                                          sign ? "arith.extsi" : "arith.extui",
                                          {args[0]},
                                          i64);
            MlirValue const divisor = select(
                mlir_cmpi(
                    loc, element, sign ? CMPI_SLE : CMPI_EQ, x, constant(0)),
                constant(1),
                x);

            std::vector<MlirValue> quotient;
            MlirValue remainder = constant(0);
            for (uint64_t const word : words) {
                auto const [q, r] = mlir_divide_narrow(
                    loc, element, remainder, constant(word), divisor);
                quotient.push_back(q);
                remainder = r;
            }
            MlirValue const high = quotient.size() >= 2
                                       ? quotient[quotient.size() - 2]
                                       : constant(0);
            MlirValue const root =
                mlir_isqrt(loc, element, high, quotient.back());

            MlirValue const max = constant(largest);
            MlirValue result =
                select(mlir_cmpi(loc, element, CMPI_UGT, root, max), max, root);
            if (exponent >= 128) {
                result = select(
                    mlir_cmpi(
                        loc,
                        element,
                        CMPI_ULE,
                        divisor,
                        constant(uint64_t{1} << (exponent - 128))),
                    max,
                    result);
            }
            return mlirTypeEqual(type, i64)
                       ? result
                       : mlir_value(
                             loc, element, "arith.trunci", {result}, type);
        });
}

// Gather: a linalg.generic over the output, which reads the index for each
// element from `indices`, through the output's dimensions that are the
// indices', and the element with tensor.extract, at the output's indices
// before and after those and the index along the axis. A signed index is
// sign-extended, so a negative one is larger than any unsigned length.
//
// TODO: report an index outside [0, n), an IndexError for the interpreter.
// Here it's clamped to n - 1, so that reading the data can't go out of bounds,
// and the element is wrong. If n is 0, there's nothing to read, and the
// elements are 0
MlirValue Compiler::mlir_op(
    GatherOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    size_t const axis = op.params;
    Shape const &data_shape = gc_.tensor_types()[op.input_ids[0]].shape();
    TensorType const &indices = gc_.tensor_types()[op.input_ids[1]];
    TensorType const &output = gc_.tensor_types()[values.size()];
    size_t const indices_rank = indices.shape().rank();
    size_t const rank = output.shape().rank();
    MlirType const element_type = mlir_type(output.dtype());
    MlirValue const init = mlir_empty(loc, block, mlir_type(output));
    uint64_t const length = data_shape.dimensions()[axis];
    if (length == 0) {
        return mlir_fill(
            loc, block, mlir_constant(loc, block, element_type, 0), init);
    }

    std::array<MlirAffineExpr, MAX_RANK> index_exprs{};
    for (size_t i = 0; i < indices_rank; i++) {
        index_exprs[i] =
            mlirAffineDimExprGet(ctx_, static_cast<intptr_t>(axis + i));
    }
    MlirAttribute const maps[]{
        indexing_map(ctx_, rank, {index_exprs.data(), indices_rank}),
        mlirAffineMapAttrGet(mlirAffineMapMultiDimIdentityGet(
            ctx_, static_cast<intptr_t>(rank))),
    };
    std::vector<MlirAttribute> const iterator_types(
        rank, iterator_type(ctx_, false));
    MlirValue const data = values[op.input_ids[0]];
    bool const sign = is_signed(indices.dtype());
    MlirOperation const gather = mlir_generic(
        loc,
        block,
        {&values[op.input_ids[1]], 1},
        {&init, 1},
        maps,
        iterator_types,
        [&](MlirBlock const element, std::span<MlirValue const> const args) {
            MlirType const index = mlirIndexTypeGet(ctx_);
            MlirType const i64 = mlirIntegerTypeGet(ctx_, 64);
            auto const loop_index = [&](size_t const dim) {
                MlirNamedAttribute const attr = mlir_named(
                    "dim", mlirIntegerAttrGet(i64, static_cast<int64_t>(dim)));
                MlirOperationState state =
                    mlirOperationStateGet(mlir_string("linalg.index"), loc);
                mlirOperationStateAddAttributes(&state, 1, &attr);
                mlirOperationStateAddResults(&state, 1, &index);
                return mlirOperationGetResult(mlir_append(element, &state), 0);
            };
            MlirValue const position = mlir_value(
                loc,
                element,
                "arith.minui",
                {mlir_value(
                     loc,
                     element,
                     sign ? "arith.index_cast" : "arith.index_castui",
                     {args[0]},
                     index),
                 mlir_constant(
                     loc, element, index, static_cast<int64_t>(length - 1))},
                index);

            // The data tensor, then its indices
            std::vector<MlirValue> operands{data};
            for (size_t i = 0; i < axis; i++) {
                operands.push_back(loop_index(i));
            }
            operands.push_back(position);
            for (size_t i = axis + indices_rank; i < rank; i++) {
                operands.push_back(loop_index(i));
            }
            MlirOperationState extract =
                mlirOperationStateGet(mlir_string("tensor.extract"), loc);
            mlirOperationStateAddOperands(
                &extract,
                static_cast<intptr_t>(operands.size()),
                operands.data());
            mlirOperationStateAddResults(&extract, 1, &element_type);
            return std::vector<MlirValue>{
                mlirOperationGetResult(mlir_append(element, &extract), 0)};
        });
    return mlirOperationGetResult(gather, 0);
}

// tensor.concat, along the axis, a's slices first
MlirValue Compiler::mlir_op(
    ConcatOp const &op, MlirLocation loc, MlirBlock block,
    std::vector<MlirValue> const &values)
{
    MlirType const output_type = mlir_type(gc_.tensor_types()[values.size()]);
    MlirValue const operands[]{
        values[op.input_ids[0]], values[op.input_ids[1]]};
    MlirNamedAttribute const dim = mlir_named(
        "dim", mlirIntegerAttrGet(mlirIntegerTypeGet(ctx_, 64), op.params));
    MlirOperationState concat =
        mlirOperationStateGet(mlir_string("tensor.concat"), loc);
    mlirOperationStateAddOperands(&concat, 2, operands);
    mlirOperationStateAddResults(&concat, 1, &output_type);
    mlirOperationStateAddAttributes(&concat, 1, &dim);
    return mlirOperationGetResult(mlir_append(block, &concat), 0);
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

// The compiled module's bytecode, and the session and call that run its
// function. The module reads the bytecode in place, so it's freed last
struct CompiledGraph::Session
{
    struct Free
    {
        void operator()(uint8_t *const p) const
        {
            std::free(p);
        }
    };

    std::unique_ptr<uint8_t, Free> vmfb;
    iree_runtime_session_t *session = nullptr;
    iree_runtime_call_t call{};
    bool call_initialized = false;
    // The bytes the function needs for the tensors in between
    size_t transients = 0;
    // The types of the graph's inputs, then of its outputs, and their
    // dimensions as IREE takes them
    std::vector<TensorType> arguments;
    std::vector<std::array<iree_hal_dim_t, MAX_RANK>> dimensions;
    size_t n_inputs = 0;

    Session() = default;
    Session(Session const &) = delete;
    Session &operator=(Session const &) = delete;

    ~Session()
    {
        if (call_initialized) {
            iree_runtime_call_deinitialize(&call);
        }
        if (session) {
            iree_runtime_session_release(session);
        }
    }
};

CompiledGraph::CompiledGraph(std::unique_ptr<Session> session)
    : session_(std::move(session))
{
}

CompiledGraph::CompiledGraph(CompiledGraph &&) noexcept = default;
CompiledGraph &CompiledGraph::operator=(CompiledGraph &&) noexcept = default;
CompiledGraph::~CompiledGraph() = default;

Result<void> CompiledGraph::run(
    std::span<uint8_t const *const> const inputs,
    std::span<uint8_t *const> const outputs, std::span<uint8_t> const scratch)
{
    Session &s = *session_;
    MONAD_ASSERT(
        inputs.size() == s.n_inputs &&
        outputs.size() == s.arguments.size() - s.n_inputs);
    if (scratch.size() < s.transients) {
        return GraphEvalError::OutOfMemory;
    }

    iree_runtime_call_reset(&s.call);
    for (size_t i = 0; i < s.arguments.size(); i++) {
        TensorType const &type = s.arguments[i];
        // IREE doesn't write the inputs
        uint8_t *const data = i < s.n_inputs ? const_cast<uint8_t *>(inputs[i])
                                             : outputs[i - s.n_inputs];
        iree_hal_buffer_t *const buffer =
            iree_import(s.session, data, type.size_bytes());
        if (!buffer) {
            return GraphEvalError::InternalError;
        }
        iree_hal_buffer_view_t *view = nullptr;
        iree_status_t const created = iree_hal_buffer_view_create(
            buffer,
            type.shape().rank(),
            s.dimensions[i].data(),
            iree_element_type(type.dtype()),
            IREE_HAL_ENCODING_TYPE_DENSE_ROW_MAJOR,
            iree_runtime_session_host_allocator(s.session),
            &view);
        // The view holds the buffer
        iree_hal_buffer_release(buffer);
        if (!iree_ok(created)) {
            return GraphEvalError::InternalError;
        }
        bool const pushed = iree_ok(
            iree_runtime_call_inputs_push_back_buffer_view(&s.call, view));
        iree_hal_buffer_view_release(view);
        if (!pushed) {
            return GraphEvalError::InternalError;
        }
    }
    iree_hal_buffer_t *const transients =
        iree_import(s.session, scratch.data(), s.transients);
    if (!transients) {
        return GraphEvalError::InternalError;
    }
    iree_vm_ref_t transients_ref = iree_hal_buffer_move_ref(transients);
    if (!iree_ok(iree_vm_list_push_ref_move(
            iree_runtime_call_inputs(&s.call), &transients_ref))) {
        iree_vm_ref_release(&transients_ref);
        return GraphEvalError::InternalError;
    }

    if (!iree_ok(iree_runtime_call_invoke(&s.call, 0))) {
        return GraphEvalError::InternalError;
    }
    // The function returns its outputs, views of the memory in `outputs`
    for (size_t i = s.n_inputs; i < s.arguments.size(); i++) {
        iree_hal_buffer_view_t *output = nullptr;
        if (!iree_ok(iree_runtime_call_outputs_pop_front_buffer_view(
                &s.call, &output))) {
            return GraphEvalError::InternalError;
        }
        iree_hal_buffer_view_release(output);
    }
    return outcome::success();
}

// Compiles the module to IREE's VM bytecode, and makes a session that loads
// it, with the call to its function. InternalError if IREE fails, or the
// function's transients don't have a size known at compile time. If `ir` isn't
// null, it gets the module before and after IREE's pipeline, as text
//
// TODO: report IREE's diagnostics other than on stderr
Result<CompiledGraph>
Compiler::iree_compile(MlirModule const module, std::string *const ir)
{
    MlirOperation const op = mlirModuleGetOperation(module);
    if (ir) {
        *ir = "== input MLIR ==\n";
        mlirOperationPrint(
            op,
            [](MlirStringRef text, void *out) {
                static_cast<std::string *>(out)->append(text.data, text.length);
            },
            ir);
        *ir += "\n";
    }
    if (!mlirOperationVerify(op)) {
        mlirModuleDestroy(module);
        return GraphEvalError::InternalError;
    }
    auto session = std::make_unique<CompiledGraph::Session>();
    {
        iree_compiler_invocation_t *const invocation =
            ireeCompilerInvocationCreate(session_);
        ireeCompilerInvocationEnableConsoleDiagnostics(invocation);
        // The invocation owns the module from here
        bool const compiled =
            ireeCompilerInvocationImportStealModule(invocation, op) &&
            ireeCompilerInvocationPipeline(
                invocation, IREE_COMPILER_PIPELINE_STD);
        iree_compiler_output_t *output = nullptr;
        void *contents = nullptr;
        uint64_t size = 0;
        bool const written =
            compiled && !ireeCompilerOutputOpenMembuffer(&output) &&
            !ireeCompilerInvocationOutputVMBytecode(invocation, output) &&
            !ireeCompilerOutputMapMemory(output, &contents, &size);
        if (written) {
            size_t const aligned = (size + 63) / 64 * 64;
            session->vmfb.reset(
                static_cast<uint8_t *>(std::aligned_alloc(64, aligned)));
            std::memcpy(session->vmfb.get(), contents, size);
        }
        if (output) {
            ireeCompilerOutputDestroy(output);
        }
        iree_compiler_output_t *ir_output = nullptr;
        void *ir_contents = nullptr;
        uint64_t ir_size = 0;
        if (ir && compiled && !ireeCompilerOutputOpenMembuffer(&ir_output) &&
            !ireeCompilerInvocationOutputIR(invocation, ir_output) &&
            !ireeCompilerOutputMapMemory(ir_output, &ir_contents, &ir_size)) {
            *ir += "== module after IREE's pipeline (VM dialect) ==\n";
            ir->append(static_cast<char const *>(ir_contents), ir_size);
        }
        if (ir_output) {
            ireeCompilerOutputDestroy(ir_output);
        }
        ireeCompilerInvocationDestroy(invocation);
        if (!written) {
            return GraphEvalError::InternalError;
        }
        IreeDevice const &device = iree_device();
        iree_runtime_session_options_t options;
        iree_runtime_session_options_initialize(&options);
        if (!iree_ok(iree_runtime_session_create_with_device(
                device.instance,
                &options,
                device.device,
                iree_runtime_instance_host_allocator(device.instance),
                &session->session)) ||
            !iree_ok(iree_runtime_session_append_bytecode_module_from_memory(
                session->session,
                iree_make_const_byte_span(session->vmfb.get(), size),
                iree_allocator_null())) ||
            !iree_ok(iree_runtime_call_initialize_by_name(
                session->session,
                iree_make_cstring_view("module.function"),
                &session->call))) {
            return GraphEvalError::InternalError;
        }
        session->call_initialized = true;
    }

    iree_string_view_t const transients = iree_vm_function_lookup_attr_by_name(
        &session->call.function,
        iree_make_cstring_view("iree.abi.transients.size.constant"));
    auto const [end, error] = std::from_chars(
        transients.data,
        transients.data + transients.size,
        session->transients);
    if (transients.size == 0 || error != std::errc{} ||
        end != transients.data + transients.size) {
        return GraphEvalError::InternalError;
    }

    session->n_inputs = gc_.n_inputs();
    for (size_t id = 0; id < session->n_inputs; id++) {
        session->arguments.push_back(gc_.tensor_types()[id]);
    }
    for (auto const id : gc_.outputs()) {
        session->arguments.push_back(gc_.tensor_types()[id]);
    }
    for (TensorType const &type : session->arguments) {
        std::array<iree_hal_dim_t, MAX_RANK> dimensions{};
        for (size_t d = 0; d < type.shape().rank(); d++) {
            dimensions[d] = type.shape().dimensions()[d];
        }
        session->dimensions.push_back(dimensions);
    }
    return CompiledGraph{std::move(session)};
}

Result<CompiledGraph> Compiler::compile(std::string *const ir)
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
    for (size_t id = 0; id < n_inputs; id++) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<TensorType>(code_));
        input_types.push_back(mlir_type(gc_.tensor_types()[id]));
    }

    BOOST_OUTCOME_TRY(read_next<uint8_t>(code_)); // n_outputs
    std::vector<MlirType> output_types;
    for (auto const &output_id : gc_.outputs()) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<uint16_t>(code_));
        output_types.push_back(mlir_type(gc_.tensor_types()[output_id]));
    }

    // The function's arguments: the graph's inputs; then a tensor per output,
    // whose memory the caller provides and IREE writes the output into
    // (iree.abi.output); then the memory for every tensor IREE would
    // otherwise allocate for the call (iree.abi.transients). The compiled
    // module's function then has an iree.abi.transients.size.constant
    // attribute, the bytes it needs
    MlirAttribute const no_attrs = mlirDictionaryAttrGet(ctx_, 0, nullptr);
    std::vector<MlirType> arg_types{input_types};
    std::vector<MlirAttribute> arg_attrs(input_types.size(), no_attrs);
    for (size_t i = 0; i < output_types.size(); i++) {
        MlirNamedAttribute const output = mlir_named(
            "iree.abi.output",
            mlirIntegerAttrGet(
                mlirIndexTypeGet(ctx_), static_cast<int64_t>(i)));
        arg_types.push_back(output_types[i]);
        arg_attrs.push_back(mlirDictionaryAttrGet(ctx_, 1, &output));
    }
    MlirNamedAttribute const transients =
        mlir_named("iree.abi.transients", mlirUnitAttrGet(ctx_));
    arg_types.push_back(
        mlir_nonnull(mlirTypeParseGet(ctx_, mlir_string("!hal.buffer"))));
    arg_attrs.push_back(mlirDictionaryAttrGet(ctx_, 1, &transients));
    std::vector<MlirLocation> const arg_locs(arg_types.size(), loc);

    MlirBlock const body = mlirBlockCreate(
        static_cast<intptr_t>(arg_types.size()),
        arg_types.data(),
        arg_locs.data());
    MlirRegion const func_region = mlirRegionCreate();
    mlirRegionAppendOwnedBlock(func_region, body);

    MlirType func_type = mlirFunctionTypeGet(
        ctx_,
        static_cast<intptr_t>(arg_types.size()),
        arg_types.data(),
        static_cast<intptr_t>(output_types.size()),
        output_types.data());

    MlirNamedAttribute const func_attrs[]{
        mlir_named(
            "sym_name", mlirStringAttrGet(ctx_, mlir_string("function"))),
        mlir_named("function_type", mlirTypeAttrGet(func_type)),
        mlir_named(
            "arg_attrs",
            mlirArrayAttrGet(
                ctx_,
                static_cast<intptr_t>(arg_attrs.size()),
                arg_attrs.data())),
    };

    MlirOperationState func =
        mlirOperationStateGet(mlir_string("func.func"), loc);
    mlirOperationStateAddAttributes(&func, std::size(func_attrs), func_attrs);
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
                TensorType const &type =
                    gc_.tensor_types()[mlir_tensors.size()];
                MlirValue value;
                if constexpr (std::same_as<OpT, TensorRefOp>) {
                    // Reads the state, which can fail, even for a tensor
                    // without elements
                    BOOST_OUTCOME_TRY(
                        value, mlir_op(op, loc, body, mlir_tensors));
                }
                else if (type.shape().size() != 0) {
                    value = mlir_op(op, loc, body, mlir_tensors);
                }
                // A tensor without elements needs nothing computed, and IREE
                // divides by zero summarizing a dispatch that computes one
                // (AnnotateDispatchesPass)
                if (type.shape().size() == 0) {
                    value = mlir_empty(loc, body, mlir_type(type));
                }
                mlir_tensors.push_back(value);
                return outcome::success();
            }));
    }

    // The function returns the graph's outputs, which have the types of
    // func_type's results
    std::vector<MlirValue> results;
    results.reserve(gc_.outputs().size());
    for (auto const &output_id : gc_.outputs()) {
        results.push_back(mlir_tensors[output_id]);
    }
    MlirOperationState func_return =
        mlirOperationStateGet(mlir_string("func.return"), loc);
    mlirOperationStateAddOperands(
        &func_return, static_cast<intptr_t>(results.size()), results.data());
    mlir_append(body, &func_return);

    return iree_compile(module, ir);
}

Compiler::Compiler(Graphcode const &gc, State &state)
    : gc_(gc)
    , code_(gc.code_span())
    , state_(state)
    , session_(create_session())
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
    // IREE's linalg extensions, for scans
    mlir_nonnull(
        mlirContextGetOrLoadDialect(ctx_, mlir_string("iree_linalg_ext")));
    // IREE's HAL, for the !hal.buffer of the function's transients
    mlir_nonnull(mlirContextGetOrLoadDialect(ctx_, mlir_string("hal")));
    // For the fixed-point ops' divisions and square roots
    mlir_nonnull(mlirContextGetOrLoadDialect(ctx_, mlir_string("math")));
}

// Also destroys the session's context, so every module built in it must be
// destroyed first
Compiler::~Compiler()
{
    ireeCompilerSessionDestroy(session_);
}

MONAD_GRAPH_EVAL_NAMESPACE_END
