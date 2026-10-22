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

#include <category/core/assert.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/fixed_point.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/halide_compiler.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <Halide.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cctype>
#include <cmath>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <map>
#include <mutex>
#include <set>
#include <span>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// The CPU graphs are compiled for, fixed, as IREE_COMPILER_FLAGS fixes it for
// IREE, so that every node runs the same code
constexpr char const *HALIDE_TARGET =
    "x86-64-linux-tune_znver4-avx-avx2-avx512-avx512_cannonlake-"
    "avx512_skylake-avx512_zen4-f16c-fma-sse41";

// Bytes in an AVX-512 vector, the lanes of which a Func's innermost loop is
// vectorized over
constexpr int VECTOR_BYTES = 64;

// A dtype's Halide type
Halide::Type halide_type_of(Dtype const dtype)
{
    int const bits = static_cast<int>(8 * dtype_size(dtype));
    return dtype_signed(dtype) ? Halide::Int(bits) : Halide::UInt(bits);
}

// A dense row-major shape as a Halide region, innermost dimension first
Halide::Region halide_region(Shape const &shape)
{
    Halide::Region region;
    for (size_t i = 0; i < shape.rank(); i++) {
        region.emplace_back(0, shape.dimensions()[shape.rank() - 1 - i]);
    }
    return region;
}

// a + b, a - b and a * b, wrapping as WrappingAdd, WrappingSub and WideningMul
// on 64-bit types do. Halide leaves
// the overflow of 32- and 64-bit signed integers undefined, and simplifies
// assuming it doesn't happen, so those are computed unsigned
Halide::Expr wrapping_add(Halide::Expr const &a, Halide::Expr const &b)
{
    Halide::Type const type = a.type();
    if (type.can_overflow()) {
        return a + b;
    }
    Halide::Type const as_unsigned = type.with_code(halide_type_uint);
    return Halide::reinterpret(
        type,
        Halide::reinterpret(as_unsigned, a) +
            Halide::reinterpret(as_unsigned, b));
}

Halide::Expr wrapping_sub(Halide::Expr const &a, Halide::Expr const &b)
{
    Halide::Type const type = a.type();
    if (type.can_overflow()) {
        return a - b;
    }
    Halide::Type const as_unsigned = type.with_code(halide_type_uint);
    return Halide::reinterpret(
        type,
        Halide::reinterpret(as_unsigned, a) -
            Halide::reinterpret(as_unsigned, b));
}

Halide::Expr wrapping_mul(Halide::Expr const &a, Halide::Expr const &b)
{
    Halide::Type const type = a.type();
    if (type.can_overflow()) {
        return a * b;
    }
    Halide::Type const as_unsigned = type.with_code(halide_type_uint);
    return Halide::reinterpret(
        type,
        Halide::reinterpret(as_unsigned, a) *
            Halide::reinterpret(as_unsigned, b));
}

// A 128-bit two's complement value, as its high word, an int64, and its low
// one, a uint64, as Halide has no 128-bit integers
struct Wide
{
    Halide::Expr hi;
    Halide::Expr lo;
};

Halide::Expr u64(uint64_t const value)
{
    return Halide::Expr{value};
}

// The dtype's largest value
uint64_t largest_value(Dtype const dtype)
{
    unsigned const width = static_cast<unsigned>(8 * dtype_size(dtype));
    return dtype_signed(dtype) ? (uint64_t{1} << (width - 1)) - 1
                               : ~uint64_t{0} >> (64 - width);
}

Halide::Expr f64(double const value)
{
    return Halide::Internal::FloatImm::make(Halide::Float(64), value);
}

// The full product of two uint64s, from the products of their 32-bit halves,
// as Halide has no 64 x 64 -> 128-bit multiply
Wide multiply_u64(Halide::Expr const &a, Halide::Expr const &b)
{
    Halide::Type const u32 = Halide::UInt(32);
    Halide::Expr const low = u64(0xffffffff);
    Halide::Expr const a0 = Halide::cast(u32, a);
    Halide::Expr const a1 = Halide::cast(u32, a >> 32);
    Halide::Expr const b0 = Halide::cast(u32, b);
    Halide::Expr const b1 = Halide::cast(u32, b >> 32);
    Halide::Expr const p00 = Halide::widening_mul(a0, b0);
    Halide::Expr const p01 = Halide::widening_mul(a0, b1);
    Halide::Expr const p10 = Halide::widening_mul(a1, b0);
    Halide::Expr const p11 = Halide::widening_mul(a1, b1);
    Halide::Expr const middle = (p00 >> 32) + (p01 & low) + (p10 & low);
    Halide::Expr const high = p11 + (p01 >> 32) + (p10 >> 32) + (middle >> 32);
    return Wide{
        Halide::reinterpret(Halide::Int(64), high),
        (middle << 32) | (p00 & low)};
}

Wide add(Wide const &a, Wide const &b)
{
    Halide::Expr const lo = a.lo + b.lo;
    return Wide{a.hi + b.hi + Halide::cast<int64_t>(lo < a.lo), lo};
}

Wide subtract(Wide const &a, Wide const &b)
{
    return Wide{a.hi - b.hi - Halide::cast<int64_t>(a.lo < b.lo), a.lo - b.lo};
}

Wide select(Halide::Expr const &condition, Wide const &yes, Wide const &no)
{
    return Wide{
        Halide::select(condition, yes.hi, no.hi),
        Halide::select(condition, yes.lo, no.lo)};
}

// A call's context: its handlers allocate the tensors computed in between in
// the call's scratch memory, bumping an offset into it, as the IREE functions
// do in their transients, and record errors, which run() reports, instead of
// throwing them. The offset is atomic, as a schedule with parallel loops
// allocates from Halide's worker threads
struct CallContext : Halide::JITUserContext
{
    uint8_t *base; // VECTOR_BYTES-aligned
    size_t capacity;
    std::atomic<size_t> used{0};
};

void *scratch_malloc(Halide::JITUserContext *const context, size_t const size)
{
    auto &call = static_cast<CallContext &>(*context);
    if (size > call.capacity) {
        return nullptr;
    }
    // Halide wants at least 32-byte alignment, which whole vectors keep
    size_t const rounded =
        (size + VECTOR_BYTES - 1) & ~static_cast<size_t>(VECTOR_BYTES - 1);
    size_t const offset =
        call.used.fetch_add(rounded, std::memory_order_relaxed);
    if (offset > call.capacity || rounded > call.capacity - offset) {
        return nullptr;
    }
    return call.base + offset;
}

void scratch_free(Halide::JITUserContext *, void *) {}

void record_error(Halide::JITUserContext *, char const *) {}

// Loads the autoscheduler plugin `name`, once per process, from the Halide
// build monad was built with
void load_autoscheduler(std::string const &name)
{
    static std::mutex mutex;
    static std::set<std::string> loaded;
    std::lock_guard const lock{mutex};
    if (loaded.contains(name)) {
        return;
    }
    std::string lower = name;
    std::ranges::transform(lower, lower.begin(), [](unsigned char const c) {
        return static_cast<char>(std::tolower(c));
    });
    Halide::load_plugin(
        std::string{MONAD_HALIDE_AUTOSCHEDULERS_DIR} + "/" + lower +
        "/libautoschedule_" + lower + ".so");
    loaded.insert(name);
}

// Makes every loop that the Funcs computing `outputs` run in parallel, and
// every producer they run asynchronously, serial, so that the pipeline runs on
// the calling thread alone. Halide runs parallel loops through its thread
// pool, and a JITUserContext's handlers can only replace that for loops that
// aren't nested in others
void make_serial(std::vector<Halide::Func> const &outputs)
{
    std::map<std::string, Halide::Internal::Function> functions;
    for (Halide::Func const &output : outputs) {
        functions.merge(
            Halide::Internal::find_transitive_calls(output.function()));
        functions.emplace(output.name(), output.function());
    }
    auto const serialize = [](Halide::Internal::Definition &definition) {
        for (auto &dim : definition.schedule().dims()) {
            if (dim.for_type == Halide::Internal::ForType::Parallel) {
                dim.for_type = Halide::Internal::ForType::Serial;
            }
        }
    };
    for (auto &[name, function] : functions) {
        function.schedule().async() = false;
        serialize(function.definition());
        for (size_t i = 0; i < function.updates().size(); i++) {
            serialize(function.update(static_cast<int>(i)));
        }
    }
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

HalideCompiledGraph::HalideCompiledGraph(
    Halide::Callable callable, std::vector<Halide::Buffer<>> constants,
    std::vector<TensorType> arguments, size_t const n_inputs)
    : callable_(std::move(callable))
    , constants_(std::move(constants))
    , arguments_(std::move(arguments))
    , n_inputs_(n_inputs)
{
    MONAD_ASSERT(
        arguments_.size() <= MAX_GRAPH_INPUTS + MAX_GRAPH_OUTPUTS &&
        n_inputs_ <= arguments_.size());
    dimensions_.reserve(arguments_.size());
    for (TensorType const &type : arguments_) {
        Shape const &shape = type.shape();
        std::array<halide_dimension_t, MAX_RANK> dimensions{};
        int32_t stride = 1;
        for (size_t i = 0; i < shape.rank(); i++) {
            int32_t const extent = shape.dimensions()[shape.rank() - 1 - i];
            dimensions[i] = halide_dimension_t{0, extent, stride};
            stride *= extent;
        }
        dimensions_.push_back(dimensions);
    }
}

// The pipeline's arguments are the call's context, then a pointer to each
// scalar input's value, and a halide_buffer_t per other input and per output
// with elements, which describes memory of the caller's, as the calling
// convention of compiled Halide pipelines has them
Result<void> HalideCompiledGraph::run(
    std::span<uint8_t const *const> const inputs,
    std::span<uint8_t *const> const outputs,
    std::span<uint8_t> const scratch) const
{
    MONAD_ASSERT(
        inputs.size() == n_inputs_ &&
        outputs.size() == arguments_.size() - n_inputs_);
    if (!callable_.defined()) {
        return outcome::success();
    }
    constexpr size_t MAX_ARGUMENTS = MAX_GRAPH_INPUTS + MAX_GRAPH_OUTPUTS;

    std::array<halide_buffer_t, MAX_ARGUMENTS> buffers{};
    std::array<void const *, 1 + MAX_ARGUMENTS> argv{};
    size_t argc = 1;
    for (size_t i = 0; i < arguments_.size(); i++) {
        TensorType const &type = arguments_[i];
        if (i < n_inputs_ && type.shape().rank() == 0) {
            argv[argc++] = inputs[i];
            continue;
        }
        if (i >= n_inputs_ && type.size_bytes() == 0) {
            continue;
        }
        halide_buffer_t &buffer = buffers[i];
        // Halide doesn't write its inputs
        buffer.host = i < n_inputs_ ? const_cast<uint8_t *>(inputs[i])
                                    : outputs[i - n_inputs_];
        buffer.type = halide_type_of(type.dtype()).to_abi();
        buffer.dimensions = static_cast<int32_t>(type.shape().rank());
        // Nor the dimensions of buffers with memory
        buffer.dim = const_cast<halide_dimension_t *>(dimensions_[i].data());
        argv[argc++] = &buffer;
    }

    // Halide may read a few bytes past an allocation's end, so the last
    // vector is left out
    auto const address = reinterpret_cast<uintptr_t>(scratch.data());
    size_t const padding =
        std::min<size_t>(scratch.size(), (-address) & (VECTOR_BYTES - 1));
    size_t const skip =
        std::min<size_t>(scratch.size(), padding + VECTOR_BYTES);
    CallContext context{};
    context.base = scratch.data() + padding;
    context.capacity = scratch.size() - skip;
    context.handlers.custom_malloc = scratch_malloc;
    context.handlers.custom_free = scratch_free;
    context.handlers.custom_error = record_error;
    Halide::JITUserContext *const context_pointer = &context;
    argv[0] = static_cast<void const *>(&context_pointer);
    int const status =
        callable_.call_argv_fast(static_cast<int>(argc), argv.data());
    if (status == halide_error_code_out_of_memory) {
        return GraphEvalError::OutOfMemory;
    }
    if (status != 0) {
        return GraphEvalError::InternalError;
    }
    return outcome::success();
}

Halide::Type HalideCompiler::halide_type(Dtype const dtype)
{
    return halide_type_of(dtype);
}

// The loop variables of a Func of `rank` dimensions, innermost first
std::vector<Halide::Var> HalideCompiler::halide_vars(size_t const rank)
{
    return {vars_.begin(), vars_.begin() + static_cast<ptrdiff_t>(rank)};
}

// Constrains an input's or output's buffer to `shape`, dense and row-major,
// so that Halide compiles for those extents and strides
void HalideCompiler::halide_constrain(
    Halide::OutputImageParam buffer, Shape const &shape)
{
    int stride = 1;
    for (size_t i = 0; i < shape.rank(); i++) {
        int const extent = shape.dimensions()[shape.rank() - 1 - i];
        buffer.dim(static_cast<int>(i))
            .set_bounds(0, extent)
            .set_stride(stride);
        stride *= extent;
    }
}

// Vectorizes a Func's pure definition along its innermost dimension, in
// AVX-512 vectors, if it's at least that long
void HalideCompiler::halide_vectorize(
    Halide::Func &func, TensorType const &type)
{
    Shape const &shape = type.shape();
    int const lanes = VECTOR_BYTES / static_cast<int>(dtype_size(type.dtype()));
    if (shape.rank() > 0 && shape.dimensions()[shape.rank() - 1] >= lanes) {
        func.vectorize(vars_[0], lanes);
    }
}

// The element of an input of `input` shape that the element of `output`
// shape at `vars` reads, broadcasting as numpy does: the input's dimensions
// line up with the output's last ones, which are its Func's first ones, and a
// dimension of 1 is read at 0 along a longer counterpart
Halide::Expr HalideCompiler::halide_element(
    Halide::Func const &input, Shape const &input_shape,
    Shape const &output_shape, std::vector<Halide::Var> const &vars)
{
    std::vector<Halide::Expr> args;
    args.reserve(input_shape.rank());
    for (size_t i = 0; i < input_shape.rank(); i++) {
        bool const same =
            input_shape.dimensions()[input_shape.rank() - 1 - i] ==
            output_shape.dimensions()[output_shape.rank() - 1 - i];
        args.push_back(same ? Halide::Expr{vars[i]} : Halide::Expr{0});
    }
    return input(args);
}

// A constant tensor: a scalar is an expression, which Halide folds into the
// ops reading it, and anything else a buffer, which the pipeline reads
Halide::Func HalideCompiler::halide_constant(
    TensorType const &type, std::span<uint8_t const> const data)
{
    Shape const &shape = type.shape();
    Halide::Func constant;
    if (shape.rank() == 0) {
        constant() = visit_dtype(type.dtype(), [&]<typename T>() {
            T value;
            std::memcpy(&value, data.data(), sizeof value);
            return Halide::Expr{value};
        });
        return constant;
    }
    std::vector<int> sizes;
    for (size_t i = 0; i < shape.rank(); i++) {
        sizes.push_back(shape.dimensions()[shape.rank() - 1 - i]);
    }
    Halide::Buffer<> buffer{halide_type(type.dtype()), sizes};
    std::memcpy(buffer.data(), data.data(), data.size());
    constants_.push_back(buffer);
    std::vector<Halide::Var> const vars = halide_vars(shape.rank());
    constant(vars) =
        clamp_reads_
            ? Halide::BoundaryConditions::repeat_edge(buffer)(vars)
            : buffer(std::vector<Halide::Expr>{vars.begin(), vars.end()});
    return constant;
}

// The input's elements combined along the axis, with wrapping adds for `sum`,
// from 0, and max otherwise, from the dtype's smallest value: a Func whose
// extent along the axis is 1, with an update over an RDom along it. An empty
// axis gives the start, with no RDom, which crashes Adams2019, as for MatMul
Halide::Func HalideCompiler::halide_reduce(
    size_t const axis, size_t const input_id,
    std::vector<Halide::Func> const &values, bool const sum)
{
    TensorType const &input = gc_.tensor_types()[input_id];
    Shape const &shape = input.shape();
    Halide::Type const type = halide_type(input.dtype());
    std::vector<Halide::Var> const vars = halide_vars(shape.rank());
    Halide::Func reduced;
    reduced(vars) = sum ? Halide::cast(type, 0) : type.min();
    int const length = shape.dimensions()[axis];
    if (length == 0) {
        return reduced;
    }
    Halide::RDom const r{0, length};
    std::vector<Halide::Expr> at{vars.begin(), vars.end()};
    at[shape.rank() - 1 - axis] = r;
    Halide::Expr const element = values[input_id](at);
    reduced(vars) = sum ? wrapping_add(reduced(vars), element)
                        : Halide::max(reduced(vars), element);
    return reduced;
}

// A Func computing the tensor of the next node, values.size(), element by
// element from the tensors of `input_ids`, broadcast to its shape. `body`
// returns its element from theirs
template <typename Body>
Halide::Func HalideCompiler::halide_elementwise(
    std::span<size_t const> const input_ids,
    std::vector<Halide::Func> const &values, Body const &body)
{
    Shape const &output = gc_.tensor_types()[values.size()].shape();
    std::vector<Halide::Var> const vars = halide_vars(output.rank());
    std::vector<Halide::Expr> elements;
    elements.reserve(input_ids.size());
    for (size_t const id : input_ids) {
        elements.push_back(halide_element(
            values[id], gc_.tensor_types()[id].shape(), output, vars));
    }
    Halide::Func result;
    result(vars) = body(std::span<Halide::Expr const>{elements});
    return result;
}

Halide::Func HalideCompiler::halide_op(
    LiteralOp const &op, std::vector<Halide::Func> const &)
{
    auto const &[type, data] = op.params;
    return halide_constant(type, data);
}

// TensorRef: the tensor in the account's code, read now, as the interpreter
// reads it when it evaluates the graph, and baked into the pipeline as a
// constant, as a Literal is. InvalidTensorRef if it doesn't match its type.
//
// TODO: as for Compiler's TensorRef, the compiled graph is then only valid
// while the account has the same code, so a cache of compiled graphs should be
// keyed by the code hashes of the accounts its TensorRefs read too
Result<Halide::Func> HalideCompiler::halide_op(
    TensorRefOp const &op, std::vector<Halide::Func> const &)
{
    auto const &[type, address, offset] = op.params;
    std::vector<uint8_t> data(type.size_bytes());
    Tensor tensor{type, data.data()};
    BOOST_OUTCOME_TRY(load_code_tensor(
        state_, CodeRef{address, offset}, ByteOrder::LittleEndian, tensor));
    return halide_constant(type, data);
}

// Wrapping, as WrappingAdd does
Halide::Func HalideCompiler::halide_op(
    AddOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return wrapping_add(args[0], args[1]);
        });
}

Halide::Func HalideCompiler::halide_op(
    SubOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return wrapping_sub(args[0], args[1]);
        });
}

// The comparison, by the inputs' signedness, which Halide's types carry, as
// the output's uint8 0 or 1
Halide::Func HalideCompiler::halide_op(
    GreaterOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return Halide::cast<uint8_t>(args[0] > args[1]);
        });
}

// The comparison, by the inputs' signedness, as the output's uint8 0 or 1
Halide::Func HalideCompiler::halide_op(
    GeOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return Halide::cast<uint8_t>(args[0] >= args[1]);
        });
}

Halide::Func HalideCompiler::halide_op(
    EqualOp const &op, std::vector<Halide::Func> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

// The same elements, in row-major order, in the output's shape: each element
// reads the input's at the same row-major position. When the two shapes are
// the same but for dimensions of 1, each dimension longer than 1 reads the
// input's counterpart directly; otherwise the position is computed from the
// output's indices, and the input's from it
Halide::Func HalideCompiler::halide_op(
    ReshapeOp const &op, std::vector<Halide::Func> const &values)
{
    Shape const &output = gc_.tensor_types()[values.size()].shape();
    Shape const &input = gc_.tensor_types()[op.input_ids[0]].shape();
    // A shape's extents as Func dimensions, innermost first
    auto const extents = [](Shape const &shape) {
        std::vector<int> result;
        for (size_t i = 0; i < shape.rank(); i++) {
            result.push_back(shape.dimensions()[shape.rank() - 1 - i]);
        }
        return result;
    };
    std::vector<int> const output_extents = extents(output);
    std::vector<int> const input_extents = extents(input);
    std::vector<Halide::Var> const vars = halide_vars(output.rank());

    // The Func dimensions longer than 1
    auto const long_dimensions = [](std::vector<int> const &extents) {
        std::vector<size_t> result;
        for (size_t i = 0; i < extents.size(); i++) {
            if (extents[i] > 1) {
                result.push_back(i);
            }
        }
        return result;
    };
    std::vector<size_t> const output_long = long_dimensions(output_extents);
    std::vector<size_t> const input_long = long_dimensions(input_extents);
    bool const same = std::ranges::equal(
        output_long, input_long, [&](size_t const o, size_t const i) {
            return output_extents[o] == input_extents[i];
        });

    std::vector<Halide::Expr> coordinates(input.rank(), Halide::Expr{0});
    if (same) {
        for (size_t i = 0; i < input_long.size(); i++) {
            coordinates[input_long[i]] = vars[output_long[i]];
        }
    }
    else {
        Halide::Expr position = 0;
        int stride = 1;
        for (size_t i = 0; i < vars.size(); i++) {
            position += vars[i] * stride;
            stride *= output_extents[i];
        }
        stride = 1;
        for (size_t i = 0; i < coordinates.size(); i++) {
            Halide::Expr coordinate = position / stride;
            if (i + 1 < coordinates.size()) {
                coordinate = coordinate % input_extents[i];
            }
            coordinates[i] = coordinate;
            stride *= input_extents[i];
        }
    }
    Halide::Func reshaped;
    reshaped(vars) = values[op.input_ids[0]](coordinates);
    return reshaped;
}

// x where the uint8 condition is nonzero, else y
Halide::Func HalideCompiler::halide_op(
    WhereOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return Halide::select(args[0] != 0, args[1], args[2]);
        });
}

// Running sums along the axis, wrapping as CumSum's do: a Func with no pure
// definition and two updates, the first slice along the axis, then each later
// one from the one before, over an RDom. It's recorded in scans_, for the
// hand-written schedule
Halide::Func HalideCompiler::halide_op(
    CumSumOp const &op, std::vector<Halide::Func> const &values)
{
    TensorType const &type = gc_.tensor_types()[values.size()];
    Shape const &shape = type.shape();
    size_t const rank = shape.rank();
    Halide::Func const &input = values[op.input_ids[0]];
    int const length = shape.dimensions()[op.params];
    if (length <= 1) {
        return input; // Its own running sum
    }
    // The axis's Func dimension
    size_t const axis = rank - 1 - op.params;

    std::vector<Halide::Var> const vars = halide_vars(rank);
    Halide::Func sums;
    sums(vars) = Halide::undef(halide_type(type.dtype()));
    std::vector<Halide::Expr> first{vars.begin(), vars.end()};
    first[axis] = 0;
    sums(first) = input(first);
    Halide::RDom const r{1, length - 1};
    std::vector<Halide::Expr> next{vars.begin(), vars.end()};
    std::vector<Halide::Expr> previous{vars.begin(), vars.end()};
    next[axis] = r;
    previous[axis] = r - 1;
    sums(next) = wrapping_add(sums(previous), input(next));
    scans_.emplace_back(values.size(), axis);
    return sums;
}

// Converts to the dtype given as the parameter, clamping to its range, as
// Halide's saturating_cast does
Halide::Func HalideCompiler::halide_op(
    SaturateOp const &op, std::vector<Halide::Func> const &values)
{
    Halide::Type const type = halide_type(op.params);
    return halide_elementwise(
        op.input_ids, values, [&](std::span<Halide::Expr const> const args) {
            return Halide::saturating_cast(type, args[0]);
        });
}

// out[i, j] = the sum over k of x[i, k] * y[k, j], of the int8 elements as
// int32, which can't overflow: zero, then an update over an RDom along k. It's
// recorded in products_, for the hand-written schedule
Halide::Func HalideCompiler::halide_op(
    MatMulOp const &op, std::vector<Halide::Func> const &values)
{
    Shape const &x_shape = gc_.tensor_types()[op.input_ids[0]].shape();
    Halide::Func const &x = values[op.input_ids[0]];
    Halide::Func const &y = values[op.input_ids[1]];
    // Func dimensions: the column, then the row
    Halide::Var const &j = vars_[0];
    Halide::Var const &i = vars_[1];
    Halide::Func product;
    if (x_shape.dimensions()[1] == 0) {
        // No products, so every element is 0. An empty RDom crashes
        // Adams2019, which asserts, then asserts again while unwinding
        product(j, i) = Halide::Expr{int32_t{0}};
        return product;
    }
    Halide::RDom const k{0, x_shape.dimensions()[1]};
    product(j, i) = Halide::Expr{int32_t{0}};
    product(j, i) +=
        Halide::cast<int32_t>(x(k, i)) * Halide::cast<int32_t>(y(j, k));
    Shape const &output = gc_.tensor_types()[values.size()].shape();
    products_.push_back(
        Product{product, output.dimensions()[0], output.dimensions()[1]});
    return product;
}

// The row-major index of the input's largest element, the first of equal
// ones, wrapped to its dtype, as ArgMax computes it. Halide's argmax over an
// RDom of the input's dimensions, innermost first, visits the elements in
// row-major order, and only replaces its candidate with a strictly larger
// element; the coordinates it returns are then combined into the index
Halide::Func HalideCompiler::halide_op(
    ArgMaxOp const &op, std::vector<Halide::Func> const &values)
{
    TensorType const &input = gc_.tensor_types()[op.input_ids[0]];
    Halide::Type const type = halide_type(input.dtype());
    Halide::Func index;
    if (input.shape().rank() == 0) {
        index() = Halide::cast(type, 0); // Its only element
        return index;
    }
    Halide::RDom const r{halide_region(input.shape())};
    std::vector<Halide::Expr> coordinates;
    for (int i = 0; i < r.dimensions(); i++) {
        coordinates.push_back(r[i]);
    }
    Halide::Tuple const largest =
        Halide::argmax(r, values[op.input_ids[0]](coordinates));
    Halide::Expr position = Halide::cast<int64_t>(0);
    int64_t stride = 1;
    for (int i = 0; i < r.dimensions(); i++) {
        position += Halide::cast<int64_t>(largest[static_cast<size_t>(i)]) *
                    Halide::Expr{stride};
        stride *= input.shape().dimensions()
                      [input.shape().rank() - 1 - static_cast<size_t>(i)];
    }
    index() = Halide::cast(type, position);
    return index;
}

Halide::Func HalideCompiler::halide_op(
    ArgMinOp const &op, std::vector<Halide::Func> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

Halide::Func HalideCompiler::halide_op(
    ClipOp const &op, std::vector<Halide::Func> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

// The larger element, by the inputs' signedness, which Halide's types carry
Halide::Func HalideCompiler::halide_op(
    MaxOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return Halide::max(args[0], args[1]);
        });
}

// The smaller element, by the inputs' signedness
Halide::Func HalideCompiler::halide_op(
    MinOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return Halide::min(args[0], args[1]);
        });
}

// The product in the type twice as wide as the inputs', where it's exact, as
// Halide's widening_mul computes it, but for 64-bit inputs, whose product
// stays 64-bit and wraps, as WideningMul's do
Halide::Func HalideCompiler::halide_op(
    MulOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return args[0].type().bits() == 64
                       ? wrapping_mul(args[0], args[1])
                       : Halide::widening_mul(args[0], args[1]);
        });
}

// x / denominator, truncated toward zero, as DivOp computes it: in int64 for
// every dtype but uint64, whose quotient by the denominator's magnitude is
// negated, wrapping, for a negative denominator. Halide's own division rounds
// down, so the int64 one is div_round_to_zero's. Dividing by -1 is a
// negation, which wraps for int64's smallest value, whose quotient Halide
// leaves undefined. Validation rejected a zero denominator
Halide::Func HalideCompiler::halide_op(
    DivOp const &op, std::vector<Halide::Func> const &values)
{
    int64_t const denominator = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    return halide_elementwise(
        op.input_ids, values, [&](std::span<Halide::Expr const> const args) {
            Halide::Expr const &x = args[0];
            if (dtype == Dtype::uint64) {
                uint64_t const magnitude =
                    denominator < 0
                        ? uint64_t{0} - static_cast<uint64_t>(denominator)
                        : static_cast<uint64_t>(denominator);
                Halide::Expr const quotient = x / Halide::Expr{magnitude};
                return denominator < 0 ? Halide::Expr{uint64_t{0}} - quotient
                                       : quotient;
            }
            Halide::Expr const wide = Halide::cast<int64_t>(x);
            Halide::Expr const quotient =
                denominator == -1 ? wrapping_sub(Halide::Expr{int64_t{0}}, wide)
                                  : Halide::div_round_to_zero(
                                        wide, Halide::Expr{denominator});
            return Halide::cast(x.type(), quotient);
        });
}

Halide::Func HalideCompiler::halide_op(
    CastOp const &op, std::vector<Halide::Func> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

// The input, broadcast to the shape, as halide_elementwise broadcasts its
// inputs
Halide::Func HalideCompiler::halide_op(
    ExpandOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_elementwise(
        op.input_ids, values, [](std::span<Halide::Expr const> const args) {
            return args[0];
        });
}

// q_mul: floor(a * b / 2^bits), wrapping to the dtype, as fixed_point.hpp
// computes it, for dtypes up to 32 bits wide: widening_mul's exact product,
// in 64 bits, shifted right, arithmetically for a signed dtype.
//
// TODO: 64-bit dtypes, whose products need 128 bits
Halide::Func HalideCompiler::halide_op(
    QMulOp const &op, std::vector<Halide::Func> const &values)
{
    int const bits = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    if (dtype_size(dtype) > 4) {
        MONAD_ABORT();
    }
    Halide::Type const wide =
        dtype_signed(dtype) ? Halide::Int(64) : Halide::UInt(64);
    return halide_elementwise(
        op.input_ids, values, [&](std::span<Halide::Expr const> const args) {
            Halide::Expr const product =
                Halide::cast(wide, Halide::widening_mul(args[0], args[1]));
            return Halide::cast(args[0].type(), product >> bits);
        });
}

// q_div: a * 2^bits / b, truncated toward zero and wrapping to the dtype, as
// fixed_point.hpp computes it, when a * 2^bits fits 64 bits, with room left
// in a signed one for its quotient by -1: a 64-bit division, rounding toward
// zero, which for a signed dtype is div_round_to_zero's, as Halide's own
// division rounds down.
//
// TODO: wider dividends, which need 128 bits; and report a zero divisor, a
// DivisionByZero for the interpreter. Here it's replaced by 1, so that dividing
// can't trap, and the element is wrong
Halide::Func HalideCompiler::halide_op(
    QDivOp const &op, std::vector<Halide::Func> const &values)
{
    unsigned const bits = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = dtype_signed(dtype);
    unsigned const width = static_cast<unsigned>(8 * dtype_size(dtype));
    if (sign ? width - 1 + bits > 62 : width + bits > 64) {
        MONAD_ABORT();
    }
    Halide::Type const wide = sign ? Halide::Int(64) : Halide::UInt(64);
    return halide_elementwise(
        op.input_ids, values, [&](std::span<Halide::Expr const> const args) {
            Halide::Type const type = args[0].type();
            Halide::Expr const dividend = Halide::reinterpret(
                wide,
                Halide::reinterpret(
                    Halide::UInt(64), Halide::cast(wide, args[0]))
                    << static_cast<int>(bits));
            Halide::Expr const divisor = Halide::cast(
                wide,
                Halide::select(args[1] == 0, Halide::cast(type, 1), args[1]));
            Halide::Expr const quotient =
                sign ? Halide::div_round_to_zero(dividend, divisor)
                     : dividend / divisor;
            return Halide::cast(type, quotient);
        });
}

// q_matmul, as matmul.cpp's matmul_generic computes it, when only the low 64
// bits of its sums reach the result, as matmul() chooses 64-bit sums: for
// dtypes up to 16 bits wide, whose sums are exact in 64 bits, and when
// `bits` plus the output's width is at most 64. The sums are uint64, as Halide
// leaves the overflow of signed 64-bit integers undefined, of each product's
// low 64 bits: widening_mul's exact product for inputs up to 32 bits wide,
// and a 64-bit multiply's for 64-bit ones. A sum is then shifted right by
// `bits`, arithmetically for a signed dtype, and truncated to the output's
// dtype. The sums are recorded in products_, for the hand-written schedule.
//
// TODO: the other cases, whose 128-bit sums Halide has no integers for
Halide::Func HalideCompiler::halide_op(
    QMatMulOp const &op, std::vector<Halide::Func> const &values)
{
    auto const [bits, out_dtype] = op.params;
    TensorType const &x_type = gc_.tensor_types()[op.input_ids[0]];
    Dtype const dtype = x_type.dtype();
    if (dtype_size(dtype) > 2 && bits + 8 * dtype_size(out_dtype) > 64) {
        MONAD_ABORT();
    }
    bool const sign = dtype_signed(dtype);
    Halide::Type const u64 = Halide::UInt(64);
    auto const product = [&](Halide::Expr const &a, Halide::Expr const &b) {
        if (a.type().bits() == 64) {
            return Halide::reinterpret(u64, a) * Halide::reinterpret(u64, b);
        }
        Halide::Expr const exact = Halide::widening_mul(a, b);
        return Halide::reinterpret(
            u64, Halide::cast(sign ? Halide::Int(64) : u64, exact));
    };

    Halide::Func const &x = values[op.input_ids[0]];
    Halide::Func const &y = values[op.input_ids[1]];
    // Func dimensions: the column, then the row
    Halide::Var const &j = vars_[0];
    Halide::Var const &i = vars_[1];
    if (x_type.shape().dimensions()[1] == 0) {
        // No products, so every element is 0, as for MatMul
        Halide::Func zeros;
        zeros(j, i) = Halide::cast(halide_type(out_dtype), 0);
        return zeros;
    }
    Halide::RDom const k{0, x_type.shape().dimensions()[1]};
    Halide::Func sums;
    sums(j, i) = Halide::Expr{uint64_t{0}};
    sums(j, i) += product(x(k, i), y(j, k));
    Shape const &output = gc_.tensor_types()[values.size()].shape();
    products_.push_back(
        Product{sums, output.dimensions()[0], output.dimensions()[1]});

    Halide::Expr const sum =
        sign ? Halide::reinterpret(Halide::Int(64), sums(j, i)) : sums(j, i);
    Halide::Func result;
    result(j, i) =
        Halide::cast(halide_type(out_dtype), sum >> static_cast<int>(bits));
    return result;
}

// Wrapping, as WrappingAdd does
Halide::Func HalideCompiler::halide_op(
    ReduceSumOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_reduce(op.params, op.input_ids[0], values, true);
}

// Validation rejected an empty axis
Halide::Func HalideCompiler::halide_op(
    ReduceMaxOp const &op, std::vector<Halide::Func> const &values)
{
    return halide_reduce(op.params, op.input_ids[0], values, false);
}

// q_exp: e^(x / 2^bits), rounded down and saturating, bit for bit as
// fixed_point.hpp computes it, which works with 64 fractional bits whatever
// the dtype: v = x * 2^(64 - bits) is split by ln 2, with 64 fractional bits,
// into an integer k and a remainder r in [0, ln 2); e^r is a polynomial in
// r / 2, with 63 fractional bits, by Horner's rule; and the result is that
// times 2^(k + bits - 63). Inputs at least EXP_LIMIT from 0 saturate first, so
// that v is below EXP_LIMIT * 2^64 in magnitude, and k in [-66, 65].
//
// Halide has no 128-bit integers, so v, k ln 2 and r are Wide pairs of
// words, and each Horner step's product, 64 x 64 bits, from which bits 63 to
// 127 are kept, comes from multiply_u64. k is estimated in double precision,
// off by at most 1 at that size, then corrected once either way, as r must
// end in [0, ln 2)
Halide::Func HalideCompiler::halide_op(
    QExpOp const &op, std::vector<Halide::Func> const &values)
{
    unsigned const bits = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = dtype_signed(dtype);
    Halide::Type const type = halide_type(dtype);
    unsigned const width = static_cast<unsigned>(8 * dtype_size(dtype));
    uint64_t const largest = largest_value(dtype);
    __int128 const limit = __int128{EXP_LIMIT} << bits;
    // v / ln 2 is x times this
    double const reciprocal = std::ldexp(1.0, 64 - static_cast<int>(bits)) /
                              static_cast<double>(LN2_Q64);
    Halide::Type const i64 = Halide::Int(64);
    Halide::Type const unsigned64 = Halide::UInt(64);

    return halide_elementwise(
        op.input_ids, values, [&](std::span<Halide::Expr const> const args) {
            Halide::Expr const &x = args[0];
            Halide::Expr const ln2 = u64(LN2_Q64);

            // v = x * 2^(64 - bits), from x's 128-bit words
            Halide::Expr const lo = Halide::reinterpret(
                unsigned64, Halide::cast(sign ? i64 : unsigned64, x));
            Halide::Expr const hi =
                sign ? Halide::cast(i64, x) >> 63 : Halide::Expr{int64_t{0}};
            Wide v;
            if (bits == 0) {
                v = Wide{Halide::reinterpret(i64, lo), u64(0)};
            }
            else {
                int const up = 64 - static_cast<int>(bits);
                v = Wide{
                    Halide::reinterpret(
                        i64,
                        (Halide::reinterpret(unsigned64, hi) << up) |
                            (lo >> static_cast<int>(bits))),
                    lo << up};
            }

            // k = floor(v / ln 2), and r = v - k ln 2, in [0, ln 2)
            Halide::Expr k = Halide::cast(
                i64,
                Halide::floor(Halide::clamp(
                    Halide::cast<double>(x) * f64(reciprocal),
                    f64(-100.0),
                    f64(100.0))));
            Wide const magnitude =
                multiply_u64(Halide::cast(unsigned64, Halide::abs(k)), ln2);
            Wide const zero{Halide::Expr{int64_t{0}}, u64(0)};
            Wide const k_ln2 =
                select(k < 0, subtract(zero, magnitude), magnitude);
            Wide r = subtract(v, k_ln2);
            Wide const ln2_wide{Halide::Expr{int64_t{0}}, ln2};
            Halide::Expr const below = r.hi < 0;
            k = Halide::select(below, k - 1, k);
            r = select(below, add(r, ln2_wide), r);
            Halide::Expr const above = r.hi > 0 || (r.hi == 0 && r.lo >= ln2);
            k = Halide::select(above, k + 1, k);
            r = select(above, subtract(r, ln2_wide), r);

            // e^r, with 63 fractional bits
            Halide::Expr const r63 = r.lo >> 1;
            Halide::Expr p = u64(EXP_COEFFICIENTS[EXP_TERMS - 1]);
            for (size_t n = EXP_TERMS - 1; n-- > 0;) {
                Wide const product = multiply_u64(p, r63);
                p = u64(EXP_COEFFICIENTS[n]) +
                    ((Halide::reinterpret(unsigned64, product.hi) << 1) |
                     (product.lo >> 63));
            }

            // p * 2^shift: past the dtype for a positive shift, and 0 for one
            // of -64 or below
            Halide::Expr const shift =
                k + Halide::Expr{static_cast<int64_t>(bits) - 63};
            Halide::Expr const shifted =
                p >> Halide::cast(
                         unsigned64,
                         Halide::clamp(
                             -shift,
                             Halide::Expr{int64_t{0}},
                             Halide::Expr{int64_t{63}}));
            Halide::Expr const max = u64(largest);
            Halide::Expr result = Halide::select(
                shift > 0,
                max,
                Halide::select(
                    shift <= -64,
                    u64(0),
                    Halide::select(shifted > max, max, shifted)));
            // Past the limits, where the polynomial isn't enough
            if (sign && limit <= (__int128{1} << (width - 1))) {
                result = Halide::select(
                    x <= Halide::cast(
                             type, Halide::Expr{static_cast<int64_t>(-limit)}),
                    u64(0),
                    result);
            }
            if (limit <= static_cast<__int128>(largest)) {
                result = Halide::select(
                    x >= Halide::cast(type, u64(static_cast<uint64_t>(limit))),
                    max,
                    result);
            }
            return Halide::cast(type, result);
        });
}

// q_inv_sqrt: floor(sqrt(2^(3 bits) / x)), saturating at the dtype's largest
// value, for a positive x, as fixed_point.hpp computes it, when 2^(3 bits)
// fits 64 bits: a 64-bit division, then the root of the quotient, below 2^63,
// estimated in double precision, which is off by at most 1, and corrected
// once either way.
//
// TODO: more fractional bits, whose quotients need 128 bits; and report an x
// that isn't positive, a DivisionByZero for 0 and a DomainError for a
// negative x for the interpreter. Here it's replaced by 1, so that dividing
// can't trap, and the element is wrong
Halide::Func HalideCompiler::halide_op(
    QInvSqrtOp const &op, std::vector<Halide::Func> const &values)
{
    unsigned const exponent = 3u * op.params;
    if (exponent > 63) {
        MONAD_ABORT();
    }
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = dtype_signed(dtype);
    uint64_t const largest = largest_value(dtype);
    Halide::Type const unsigned64 = Halide::UInt(64);
    return halide_elementwise(
        op.input_ids, values, [&](std::span<Halide::Expr const> const args) {
            Halide::Expr const &x = args[0];
            Halide::Expr const positive = sign ? x > 0 : x != 0;
            Halide::Expr const divisor =
                Halide::select(positive, Halide::cast(unsigned64, x), u64(1));
            Halide::Expr const quotient =
                u64(uint64_t{1} << exponent) / divisor;
            Halide::Expr root = Halide::cast(
                unsigned64,
                Halide::floor(Halide::sqrt(Halide::cast<double>(quotient))));
            root = Halide::select(root * root > quotient, root - 1, root);
            root = Halide::select(
                (root + 1) * (root + 1) <= quotient, root + 1, root);
            Halide::Expr const max = u64(largest);
            return Halide::cast(
                x.type(), Halide::select(root > max, max, root));
        });
}

// Gather: each element reads data at the output's indices, but along the
// axis, where it reads the index in `indices` at the output's indices that
// are the indices'.
//
// The autoschedulers need the data's reads bounded by constants, but bounds
// inference bounds an index that doesn't vary, such as an element of a
// constant read at a constant position, by its symbolic value. So autoscheduled
// compiles read the indices through a Func with an identity update, as Halide
// gives a Func with updates no bounds on its values, and the clamp below
// alone bounds the reads.
//
// TODO: report an index outside [0, n), an IndexError for the interpreter.
// It's narrowed to int32 and clamped to [0, n), so that reading the data
// can't go out of bounds, and the element is wrong. If n is 0, there's nothing
// to read, and the elements are 0
Halide::Func HalideCompiler::halide_op(
    GatherOp const &op, std::vector<Halide::Func> const &values)
{
    size_t const axis = op.params;
    TensorType const &data = gc_.tensor_types()[op.input_ids[0]];
    TensorType const &indices = gc_.tensor_types()[op.input_ids[1]];
    size_t const data_rank = data.shape().rank();
    size_t const indices_rank = indices.shape().rank();
    size_t const rank = data_rank - 1 + indices_rank;
    std::vector<Halide::Var> const vars = halide_vars(rank);
    // The output's loop variable for its tensor dimension d
    auto const output_var = [&](size_t const d) {
        return Halide::Expr{vars[rank - 1 - d]};
    };
    int const length = data.shape().dimensions()[axis];
    Halide::Func gathered;
    if (length == 0) {
        gathered(vars) = Halide::cast(halide_type(data.dtype()), 0);
        return gathered;
    }

    Halide::Func index = values[op.input_ids[1]];
    if (clamp_reads_) {
        std::vector<Halide::Var> const index_vars = halide_vars(indices_rank);
        Halide::Func opaque;
        opaque(index_vars) = index(index_vars);
        opaque(index_vars) = opaque(index_vars);
        index = opaque;
    }
    std::vector<Halide::Expr> at_index(indices_rank);
    for (size_t e = 0; e < indices_rank; e++) {
        at_index[indices_rank - 1 - e] = output_var(axis + e);
    }
    Halide::Expr const position =
        Halide::clamp(Halide::cast<int32_t>(index(at_index)), 0, length - 1);
    std::vector<Halide::Expr> at_data(data_rank);
    for (size_t d = 0; d < data_rank; d++) {
        at_data[data_rank - 1 - d] = d < axis ? output_var(d)
                                     : d == axis
                                         ? position
                                         : output_var(d - 1 + indices_rank);
    }
    gathered(vars) = values[op.input_ids[0]](at_data);
    return gathered;
}

// a's slices along the axis, then b's: each element reads the one its index
// along the axis falls in, with both indices clamped into their tensors, as
// Halide's select reads both sides. An empty operand leaves the other
Halide::Func HalideCompiler::halide_op(
    ConcatOp const &op, std::vector<Halide::Func> const &values)
{
    size_t const axis = op.params;
    Shape const &a = gc_.tensor_types()[op.input_ids[0]].shape();
    Shape const &b = gc_.tensor_types()[op.input_ids[1]].shape();
    int const a_length = a.dimensions()[axis];
    int const b_length = b.dimensions()[axis];
    if (b_length == 0) {
        return values[op.input_ids[0]];
    }
    if (a_length == 0) {
        return values[op.input_ids[1]];
    }
    size_t const rank = a.rank();
    size_t const dimension = rank - 1 - axis;
    std::vector<Halide::Var> const vars = halide_vars(rank);
    Halide::Expr const index = vars[dimension];
    std::vector<Halide::Expr> in_a{vars.begin(), vars.end()};
    std::vector<Halide::Expr> in_b{vars.begin(), vars.end()};
    in_a[dimension] = Halide::min(index, a_length - 1);
    in_b[dimension] = Halide::max(index - a_length, 0);
    Halide::Func joined;
    joined(vars) = Halide::select(
        index < a_length,
        values[op.input_ids[0]](in_a),
        values[op.input_ids[1]](in_b));
    return joined;
}

// The graph as a Halide pipeline, unscheduled. Its arguments are an
// ImageParam per input, then a buffer per output, constrained to the graph's
// shapes, which are also their estimates, for the autoschedulers
Result<HalideCompiler::HalidePipeline> HalideCompiler::halide_pipeline()
{
    if (gc_.validation_result() != GraphEvalError::Success) {
        return gc_.validation_result();
    }
    HalidePipeline pipeline;

    // Read magic number
    BOOST_OUTCOME_TRY(read_next<uint16_t>(code_));

    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code_));
    pipeline.values.reserve(gc_.tensor_types().size());
    for (size_t id = 0; id < n_inputs; id++) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<TensorType>(code_));
        TensorType const &type = gc_.tensor_types()[id];
        Halide::Type const element = halide_type(type.dtype());
        size_t const rank = type.shape().rank();
        std::vector<Halide::Var> const vars = halide_vars(rank);
        Halide::Func value;
        // A scalar is a Param, whose value the autoschedulers estimate, as
        // Adams2019 needs when it picks a Gather's index: a 0-dimensional
        // ImageParam's element is a value they can't bound
        if (rank == 0) {
            Halide::Param<> input{element};
            input.set_estimate(0);
            value() = input;
            pipeline.inputs.push_back(input);
        }
        else {
            Halide::ImageParam input{element, static_cast<int>(rank)};
            halide_constrain(input, type.shape());
            input.set_estimates(halide_region(type.shape()));
            value(vars) =
                clamp_reads_
                    ? Halide::BoundaryConditions::repeat_edge(input)(vars)
                    : input(vars);
            pipeline.inputs.push_back(input);
        }
        pipeline.values.push_back(value);
        pipeline.arguments.push_back(type);
    }

    BOOST_OUTCOME_TRY(read_next<uint8_t>(code_)); // n_outputs
    for (size_t i = 0; i < gc_.outputs().size(); i++) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<uint16_t>(code_));
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code_));
    std::vector<Halide::Func> &values = pipeline.values;
    pipeline.readers.assign(gc_.tensor_types().size(), 0);
    for (size_t i = 0; i < n_ops; i++) {
        BOOST_OUTCOME_TRY(
            visit_next(code_, [&]<typename OpT>(OpT const &op) -> Result<void> {
                for (size_t const id : op.input_ids) {
                    pipeline.readers[id]++;
                }
                if constexpr (std::same_as<OpT, TensorRefOp>) {
                    // Reads the state, which can fail
                    BOOST_OUTCOME_TRY(auto const value, halide_op(op, values));
                    values.push_back(value);
                }
                else {
                    values.push_back(halide_op(op, values));
                }
                return outcome::success();
            }));
    }

    // An empty output has nothing to write, and is left out: the
    // autoschedulers would still compute some of it, reading its inputs, which
    // are empty too, as Mullapudi2016 and Li2018 do, or assert on its empty
    // loops, as Adams2019 does
    for (auto const &output_id : gc_.outputs()) {
        TensorType const &type = gc_.tensor_types()[output_id];
        pipeline.arguments.push_back(type);
        if (type.size_bytes() == 0) {
            continue;
        }
        std::vector<Halide::Var> const vars = halide_vars(type.shape().rank());
        Halide::Func output;
        output(vars) = values[output_id](vars);
        halide_constrain(output.output_buffer(), type.shape());
        output.set_estimates(halide_region(type.shape()));
        pipeline.outputs.push_back(output);
    }
    return pipeline;
}

// The hand-written schedule. Halide inlines every Func into the ones reading
// it unless told otherwise, which fuses chains of elementwise ops as IREE's
// dispatches do. A Func with updates can't be inlined, and one read by more
// than one other is computed once, so those are computed at root, in scratch
// memory; those and the outputs are vectorized. A scan's update loops along
// the axis outermost, so that its inner loops, along the other dimensions,
// are independent, and vectorized along the innermost one, with a guarded
// last vector: Halide rounds an update's loop up to whole vectors by default,
// which reads the input past its end
void HalideCompiler::halide_schedule(HalidePipeline &pipeline)
{
    std::vector<Halide::Func> &values = pipeline.values;
    for (size_t id = pipeline.inputs.size(); id < values.size(); id++) {
        Halide::Func &value = values[id];
        TensorType const &type = gc_.tensor_types()[id];
        if (value.has_update_definition()) {
            value.compute_root();
        }
        else if (pipeline.readers[id] > 1 && type.shape().rank() > 0) {
            value.compute_root();
            halide_vectorize(value, type);
        }
    }

    for (auto const &[id, axis] : scans_) {
        Halide::Func &sums = values[id];
        TensorType const &type = gc_.tensor_types()[id];
        Shape const &shape = type.shape();
        size_t const rank = shape.rank();
        std::vector<Halide::VarOrRVar> order;
        for (size_t i = 0; i < rank; i++) {
            if (i != axis) {
                order.emplace_back(vars_[i]);
            }
        }
        order.emplace_back(sums.rvars(1)[0]);
        sums.update(1).reorder(order);
        if (rank > 1) {
            // The innermost dimension but the axis
            size_t const inner = axis == 0 ? 1 : 0;
            int const lanes =
                VECTOR_BYTES / static_cast<int>(dtype_size(type.dtype()));
            if (shape.dimensions()[rank - 1 - inner] >= lanes) {
                sums.update(0).vectorize(
                    vars_[inner], lanes, Halide::TailStrategy::GuardWithIf);
                sums.update(1).vectorize(
                    vars_[inner], lanes, Halide::TailStrategy::GuardWithIf);
            }
        }
    }

    // A product's sums are computed at root. Its update loops along its rows
    // outermost, then k, then its
    // columns, which are vectorized, reading a row of y per element of x;
    // with too few columns, as for a matrix-vector product, the rows are
    // vectorized instead, innermost, each loop along k reading a column of x
    for (auto &[product, rows, columns] : products_) {
        Halide::Var const &j = vars_[0];
        Halide::Var const &i = vars_[1];
        Halide::RVar const k = product.rvars(0)[0];
        int const lanes = VECTOR_BYTES / product.type().bytes();
        product.compute_root();
        if (columns >= lanes) {
            product.vectorize(j, lanes);
            product.update().reorder(j, k, i).vectorize(
                j, lanes, Halide::TailStrategy::GuardWithIf);
        }
        else if (rows >= lanes) {
            product.reorder(i, j).vectorize(i, lanes);
            product.update().reorder(i, k, j).vectorize(
                i, lanes, Halide::TailStrategy::GuardWithIf);
        }
    }

    std::span<TensorType const> const outputs =
        std::span{pipeline.arguments}.subspan(pipeline.inputs.size());
    size_t i = 0;
    for (TensorType const &type : outputs) {
        if (type.size_bytes() != 0) {
            halide_vectorize(pipeline.outputs[i++], type);
        }
    }
}

// JIT-compiles the scheduled pipeline, which holds the graph's outputs with
// elements, unless there are none
HalideCompiledGraph HalideCompiler::halide_compile(
    HalidePipeline &pipeline, Halide::Pipeline &scheduled)
{
    Halide::Callable callable;
    if (!pipeline.outputs.empty()) {
        callable = scheduled.compile_to_callable(
            pipeline.inputs, Halide::Target{HALIDE_TARGET});
    }
    return HalideCompiledGraph{
        std::move(callable),
        std::move(constants_),
        std::move(pipeline.arguments),
        pipeline.inputs.size()};
}

Result<HalideCompiledGraph> HalideCompiler::compile()
{
    try {
        BOOST_OUTCOME_TRY(auto pipeline, halide_pipeline());
        halide_schedule(pipeline);
        Halide::Pipeline scheduled{pipeline.outputs};
        return halide_compile(pipeline, scheduled);
    }
    catch (Halide::Error const &error) {
        std::cerr << "Halide: " << error.what() << std::endl;
        return GraphEvalError::InternalError;
    }
}

// The autoscheduler gets a parallelism of 1, a single thread, unless the
// options give one, and with 1 any parallel loops it still chooses, as Li2018
// does, are made serial. Reads of the inputs and constants are clamped, as
// Adams2019, for one, computes Funcs past their extents
Result<HalideCompiledGraph>
HalideCompiler::compile(Halide::AutoschedulerParams const &scheduler)
{
    try {
        clamp_reads_ = true;
        BOOST_OUTCOME_TRY(auto pipeline, halide_pipeline());
        load_autoscheduler(scheduler.name);
        Halide::AutoschedulerParams params = scheduler;
        params.extra.try_emplace("parallelism", "1");
        Halide::Pipeline scheduled{pipeline.outputs};
        if (!pipeline.outputs.empty()) {
            scheduled.apply_autoscheduler(
                Halide::Target{HALIDE_TARGET}, params);
            if (params.extra.at("parallelism") == "1") {
                make_serial(pipeline.outputs);
            }
        }
        return halide_compile(pipeline, scheduled);
    }
    catch (Halide::Error const &error) {
        std::cerr << "Halide: " << error.what() << std::endl;
        return GraphEvalError::InternalError;
    }
}

HalideCompiler::HalideCompiler(Graphcode const &gc, State &state)
    : gc_(gc)
    , code_(gc.code_span())
    , state_(state)
{
}

MONAD_GRAPH_EVAL_NAMESPACE_END
