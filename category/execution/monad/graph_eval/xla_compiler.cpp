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
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>
#include <category/execution/monad/graph_eval/xla/monad_xla/monad_xla.h>
#include <category/execution/monad/graph_eval/xla_compiler.hpp>

#include <algorithm>
#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <format>
#include <iostream>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// The CPU XLA compiles for, as IREE and Halide do: Zen 4, which every
// validator has. LLVM derives the CPU's features from its name; these are the
// ones XLA's own options look at, AVX-512 above all, as XLA lists them for a
// host it detects
constexpr char const *XLA_CPU = "znver4";
constexpr char const *XLA_FEATURES =
    "+avx2,+avx512bf16,+avx512bitalg,+avx512bw,+avx512cd,+avx512dq,+avx512f,"
    "+avx512ifma,+avx512vbmi,+avx512vbmi2,+avx512vl,+avx512vnni,"
    "+avx512vpopcntdq,+bmi,+bmi2,+f16c,+fma,+gfni,+vaes,+vpclmulqdq";

char const *hlo_type(Dtype const dtype)
{
    switch (dtype) {
    case Dtype::int8:
        return "s8";
    case Dtype::uint8:
        return "u8";
    case Dtype::int16:
        return "s16";
    case Dtype::uint16:
        return "u16";
    case Dtype::int32:
        return "s32";
    case Dtype::uint32:
        return "u32";
    case Dtype::int64:
        return "s64";
    case Dtype::uint64:
        return "u64";
    }
    MONAD_ABORT();
}

// An array's shape as HLO writes it, such as s8[19,196], whose default layout
// is row-major
std::string
hlo_shape(std::string_view const type, std::span<uint16_t const> dims)
{
    std::string shape{type};
    shape += '[';
    for (size_t i = 0; i < dims.size(); i++) {
        shape += std::format("{}{}", i == 0 ? "" : ",", dims[i]);
    }
    shape += ']';
    return shape;
}

std::string hlo_shape(Dtype const dtype, Shape const &shape)
{
    return hlo_shape(
        hlo_type(dtype), std::span{shape.dimensions()}.first(shape.rank()));
}

std::string hlo_shape(TensorType const &type)
{
    return hlo_shape(type.dtype(), type.shape());
}

std::string hlo_pred_shape(Shape const &shape)
{
    return hlo_shape("pred", std::span{shape.dimensions()}.first(shape.rank()));
}

// A dtype's smallest and largest values
std::pair<__int128, __int128> dtype_range(Dtype const dtype)
{
    int const bits = static_cast<int>(8 * dtype_size(dtype));
    if (dtype_signed(dtype)) {
        return {-(__int128{1} << (bits - 1)), (__int128{1} << (bits - 1)) - 1};
    }
    return {0, (__int128{1} << bits) - 1};
}

std::string decimal(__int128 const value)
{
    if (value == 0) {
        return "0";
    }
    unsigned __int128 magnitude =
        value < 0 ? 0 - static_cast<unsigned __int128>(value)
                  : static_cast<unsigned __int128>(value);
    std::string digits;
    while (magnitude != 0) {
        digits += static_cast<char>('0' + static_cast<int>(magnitude % 10));
        magnitude /= 10;
    }
    if (value < 0) {
        digits += '-';
    }
    std::reverse(digits.begin(), digits.end());
    return digits;
}

// A literal's elements as HLO writes an array: nested braces, row-major, from
// dimension `d` on, starting at element `index`
void append_elements(
    std::string &out, TensorType const &type, std::span<uint8_t const> bytes,
    size_t const d, size_t &index)
{
    Shape const &shape = type.shape();
    if (d == shape.rank()) {
        visit_dtype(type.dtype(), [&]<typename T>() {
            T element;
            std::memcpy(&element, bytes.data() + index * sizeof(T), sizeof(T));
            out += decimal(element);
        });
        index++;
        return;
    }
    out += '{';
    for (size_t i = 0; i < shape.dimensions()[d]; i++) {
        if (i != 0) {
            out += ", ";
        }
        append_elements(out, type, bytes, d + 1, index);
    }
    out += '}';
}

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

void XlaCompiledGraph::Destroy::operator()(
    monad_xla_executable *const executable) const
{
    monad_xla_destroy(executable);
}

XlaCompiledGraph::XlaCompiledGraph(
    monad_xla_executable *const executable, size_t const n_inputs,
    size_t const n_outputs)
    : executable_(executable)
    , n_inputs_(n_inputs)
    , n_outputs_(n_outputs)
    , temp_size_(monad_xla_temp_size(executable))
{
    MONAD_ASSERT(
        n_inputs_ <= MAX_GRAPH_INPUTS && n_outputs_ <= MAX_GRAPH_OUTPUTS);
}

Result<void> XlaCompiledGraph::run(
    std::span<uint8_t const *const> const inputs,
    std::span<uint8_t *const> const outputs,
    std::span<uint8_t> const scratch) const
{
    MONAD_ASSERT(inputs.size() == n_inputs_ && outputs.size() == n_outputs_);
    if (scratch.size() < temp_size_) {
        return GraphEvalError::OutOfMemory;
    }
    std::array<void const *, MAX_GRAPH_INPUTS> parameters{};
    std::array<void *, MAX_GRAPH_OUTPUTS> results{};
    std::copy(inputs.begin(), inputs.end(), parameters.begin());
    std::copy(outputs.begin(), outputs.end(), results.begin());
    if (monad_xla_run(
            executable_.get(),
            parameters.data(),
            results.data(),
            scratch.data()) != MONAD_XLA_OK) {
        return GraphEvalError::InternalError;
    }
    return outcome::success();
}

std::string XlaCompiler::hlo_name()
{
    return std::format("v{}", next_name_++);
}

// Appends `instruction`, of shape `shape`, to the entry computation, and
// returns its name
std::string XlaCompiler::hlo_append(
    std::string_view const shape, std::string_view const instruction)
{
    std::string name = hlo_name();
    entry_ += std::format("  {} = {} {}\n", name, shape, instruction);
    return name;
}

std::string XlaCompiler::hlo_constant(Dtype const dtype, __int128 const value)
{
    return hlo_append(
        std::format("{}[]", hlo_type(dtype)),
        std::format("constant({})", decimal(value)));
}

// A tensor of `shape` whose every element is `value`
std::string XlaCompiler::hlo_splat(
    Dtype const dtype, __int128 const value, Shape const &shape)
{
    std::string scalar = hlo_constant(dtype, value);
    if (shape.rank() == 0) {
        return scalar;
    }
    return hlo_append(
        hlo_shape(dtype, shape),
        std::format("broadcast({}), dimensions={{}}", scalar));
}

// `value`, of `type`, broadcast to `shape` as numpy broadcasts: its dimensions
// line up with the shape's last ones, and one of size 1 repeats. HLO's
// broadcast only maps dimensions, so those of size 1 that repeat are reshaped
// away first
std::string XlaCompiler::hlo_broadcast(
    std::string const &value, TensorType const &type, Shape const &shape)
{
    Shape const &from = type.shape();
    if (from == shape) {
        return value;
    }
    size_t const offset = shape.rank() - from.rank();
    std::vector<uint16_t> kept;
    std::string mapped;
    for (size_t i = 0; i < from.rank(); i++) {
        if (from.dimensions()[i] == shape.dimensions()[offset + i]) {
            kept.push_back(from.dimensions()[i]);
            mapped +=
                std::format("{}{}", mapped.empty() ? "" : ",", offset + i);
        }
    }
    std::string source = value;
    if (kept.size() != from.rank()) {
        source = hlo_append(
            hlo_shape(hlo_type(type.dtype()), kept),
            std::format("reshape({})", value));
    }
    return hlo_append(
        hlo_shape(type.dtype(), shape),
        std::format("broadcast({}), dimensions={{{}}}", source, mapped));
}

std::string XlaCompiler::hlo_convert(
    std::string const &value, Dtype const dtype, Shape const &shape)
{
    return hlo_append(
        hlo_shape(dtype, shape), std::format("convert({})", value));
}

// The computation ArgMax reduces (value, index) pairs with: the larger value,
// and of equal values, the smaller index, which is the first, as the
// interpreter picks. Indices are s32: tensors fit in the arena
std::string XlaCompiler::hlo_argmax_computation(Dtype const dtype)
{
    std::string const name = std::format("argmax_{}", hlo_type(dtype));
    if (computation_names_.insert(name).second) {
        std::string const scalar = std::format("{}[]", hlo_type(dtype));
        computations_ += std::format(
            "{0} {{\n"
            "  {0}_av = {1} parameter(0)\n"
            "  {0}_ai = s32[] parameter(1)\n"
            "  {0}_bv = {1} parameter(2)\n"
            "  {0}_bi = s32[] parameter(3)\n"
            "  {0}_gt = pred[] compare({0}_av, {0}_bv), direction=GT\n"
            "  {0}_eq = pred[] compare({0}_av, {0}_bv), direction=EQ\n"
            "  {0}_lt = pred[] compare({0}_ai, {0}_bi), direction=LT\n"
            "  {0}_tie = pred[] and({0}_eq, {0}_lt)\n"
            "  {0}_a = pred[] or({0}_gt, {0}_tie)\n"
            "  {0}_v = {1} select({0}_a, {0}_av, {0}_bv)\n"
            "  {0}_i = s32[] select({0}_a, {0}_ai, {0}_bi)\n"
            "  ROOT {0}_r = ({1}, s32[]) tuple({0}_v, {0}_i)\n"
            "}}\n\n",
            name,
            scalar);
    }
    return name;
}

std::vector<std::string> XlaCompiler::hlo_operands(
    std::span<size_t const> const input_ids,
    std::vector<std::string> const &values)
{
    Shape const &shape = gc_.tensor_types()[values.size()].shape();
    std::vector<std::string> operands;
    for (size_t const id : input_ids) {
        operands.push_back(
            hlo_broadcast(values[id], gc_.tensor_types()[id], shape));
    }
    return operands;
}

// The next node, values.size(), computed by `body` from its inputs, broadcast
// to its shape, and its type
template <typename F>
std::string XlaCompiler::hlo_elementwise(
    std::span<size_t const> const input_ids,
    std::vector<std::string> const &values, F const &body)
{
    TensorType const &type = gc_.tensor_types()[values.size()];
    return body(hlo_operands(input_ids, values), type);
}

std::string
XlaCompiler::xla_op(LiteralOp const &op, std::vector<std::string> const &)
{
    auto const &[type, bytes] = op.params;
    std::string elements;
    size_t index = 0;
    append_elements(elements, type, bytes, 0, index);
    return hlo_append(hlo_shape(type), std::format("constant({})", elements));
}

Result<std::string> XlaCompiler::xla_op(
    TensorRefOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

// Add, Sub, Max and Min wrap, or compare by the dtype's signedness, as XLA's
// emitters do for integers [XLA_LOWERING.md]
std::string
XlaCompiler::xla_op(AddOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            return hlo_append(
                hlo_shape(type), std::format("add({}, {})", args[0], args[1]));
        });
}

std::string
XlaCompiler::xla_op(SubOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            return hlo_append(
                hlo_shape(type),
                std::format("subtract({}, {})", args[0], args[1]));
        });
}

// The comparison, by the inputs' signedness, as the output's uint8 0 or 1
std::string
XlaCompiler::xla_op(GreaterOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            std::string const compare = hlo_append(
                hlo_pred_shape(type.shape()),
                std::format("compare({}, {}), direction=GT", args[0], args[1]));
            return hlo_convert(compare, Dtype::uint8, type.shape());
        });
}

std::string
XlaCompiler::xla_op(GeOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(EqualOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

// HLO's reshape is row-major, as graph_eval's tensors are
std::string
XlaCompiler::xla_op(ReshapeOp const &op, std::vector<std::string> const &values)
{
    TensorType const &type = gc_.tensor_types()[values.size()];
    return hlo_append(
        hlo_shape(type), std::format("reshape({})", values[op.input_ids[0]]));
}

std::string
XlaCompiler::xla_op(WhereOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            std::string const zero = hlo_splat(Dtype::uint8, 0, type.shape());
            std::string const condition = hlo_append(
                hlo_pred_shape(type.shape()),
                std::format("compare({}, {}), direction=NE", args[0], zero));
            return hlo_append(
                hlo_shape(type),
                std::format("select({}, {}, {})", condition, args[1], args[2]));
        });
}

// Running sums along the axis, which wrap, so any order of additions gives the
// interpreter's, as a while loop along the axis: each iteration reads one
// slice of the input, adds it to the running sum and writes the sum into the
// output, which XLA updates in place. The work per element is the same at any
// length, and the time doesn't depend on what XLA fuses. Not a reduce-window,
// which XLA's CPU backend computes for each element on its own, adding the
// whole axis's window with a bounds check per position. LLVM vectorizes those
// checks into masked loads, which for positions in the padding have every
// element masked off but an address up to the axis's length of rows before
// the input; on Zen 4, each such load costs ~160 extra cycles when the page at
// its address isn't present (unmapped, or mapped but never written). At
// 10 x 500 x 500 that took 3 ms or 100 ms depending on what was below the
// input. An empty tensor, or an axis of 1, is its own
std::string
XlaCompiler::xla_op(CumSumOp const &op, std::vector<std::string> const &values)
{
    size_t const axis = op.params;
    size_t const id = op.input_ids[0];
    TensorType const &type = gc_.tensor_types()[id];
    std::span const dims =
        std::span{type.shape().dimensions()}.first(type.shape().rank());
    if (type.shape().size() == 0 || dims[axis] == 1) {
        return values[id];
    }
    std::vector<uint16_t> row(dims.begin(), dims.end());
    row[axis] = 1;
    std::string const shape = hlo_shape(type);
    std::string const row_shape = hlo_shape(hlo_type(type.dtype()), row);
    std::string const state =
        std::format("(s32[], {0}, {1}, {0})", shape, row_shape);
    std::string const name = std::format("cumsum_{}", hlo_name());
    std::string starts;
    std::string sizes;
    for (size_t d = 0; d < dims.size(); d++) {
        starts += std::format(
            "{}{}_{}", d == 0 ? "" : ", ", name, d == axis ? "i" : "zero");
        sizes += std::format("{}{}", d == 0 ? "" : ",", row[d]);
    }
    computations_ += std::format(
        "{0}_body {{\n"
        "  {0}_state = {1} parameter(0)\n"
        "  {0}_i = s32[] get-tuple-element({0}_state), index=0\n"
        "  {0}_x = {2} get-tuple-element({0}_state), index=1\n"
        "  {0}_sum = {3} get-tuple-element({0}_state), index=2\n"
        "  {0}_out = {2} get-tuple-element({0}_state), index=3\n"
        "  {0}_zero = s32[] constant(0)\n"
        "  {0}_slice = {3} dynamic-slice({0}_x, {4}), "
        "dynamic_slice_sizes={{{5}}}\n"
        "  {0}_next_sum = {3} add({0}_sum, {0}_slice)\n"
        "  {0}_next_out = {2} dynamic-update-slice({0}_out, {0}_next_sum, "
        "{4})\n"
        "  {0}_one = s32[] constant(1)\n"
        "  {0}_next_i = s32[] add({0}_i, {0}_one)\n"
        "  ROOT {0}_next = {1} tuple({0}_next_i, {0}_x, {0}_next_sum, "
        "{0}_next_out)\n"
        "}}\n\n"
        "{0}_condition {{\n"
        "  {0}_condition_state = {1} parameter(0)\n"
        "  {0}_condition_i = s32[] get-tuple-element({0}_condition_state), "
        "index=0\n"
        "  {0}_length = s32[] constant({6})\n"
        "  ROOT {0}_more = pred[] compare({0}_condition_i, {0}_length), "
        "direction=LT\n"
        "}}\n\n",
        name,
        state,
        shape,
        row_shape,
        starts,
        sizes,
        dims[axis]);
    std::string const i = hlo_append("s32[]", "constant(0)");
    std::string const zero = hlo_constant(type.dtype(), 0);
    std::string const sum = hlo_append(
        row_shape, std::format("broadcast({}), dimensions={{}}", zero));
    std::string const out =
        hlo_append(shape, std::format("broadcast({}), dimensions={{}}", zero));
    std::string const init = hlo_append(
        state, std::format("tuple({}, {}, {}, {})", i, values[id], sum, out));
    std::string const loop = hlo_append(
        state,
        std::format(
            "while({}), condition={}_condition, body={}_body",
            init,
            name,
            name));
    return hlo_append(
        shape, std::format("get-tuple-element({}), index=3", loop));
}

// Values outside the output dtype's range are clamped to it in the input's
// dtype, which holds both of the bounds it clamps to, then converted
std::string XlaCompiler::xla_op(
    SaturateOp const &op, std::vector<std::string> const &values)
{
    Dtype const to = op.params;
    size_t const id = op.input_ids[0];
    TensorType const &input = gc_.tensor_types()[id];
    Dtype const from = input.dtype();
    Shape const &shape = input.shape();
    auto const [from_min, from_max] = dtype_range(from);
    auto const [to_min, to_max] = dtype_range(to);
    std::string value = values[id];
    if (from_max > to_max) {
        value = hlo_append(
            hlo_shape(input),
            std::format(
                "minimum({}, {})", value, hlo_splat(from, to_max, shape)));
    }
    if (from_min < to_min) {
        value = hlo_append(
            hlo_shape(input),
            std::format(
                "maximum({}, {})", value, hlo_splat(from, to_min, shape)));
    }
    return from == to ? value : hlo_convert(value, to, shape);
}

// int8 x int8 -> int32, which XLA allows as a dot of mixed precision. Its
// sums can't overflow: even 65535 products of -128 and -128 fit
std::string
XlaCompiler::xla_op(MatMulOp const &op, std::vector<std::string> const &values)
{
    TensorType const &type = gc_.tensor_types()[values.size()];
    return hlo_append(
        hlo_shape(type),
        std::format(
            "dot({}, {}), lhs_contracting_dims={{1}}, "
            "rhs_contracting_dims={{0}}",
            values[op.input_ids[0]],
            values[op.input_ids[1]]));
}

// A variadic reduce over the flattened input and its indices, keeping the
// first of the largest, whose index wraps to the input's dtype, as the
// interpreter's does
std::string
XlaCompiler::xla_op(ArgMaxOp const &op, std::vector<std::string> const &values)
{
    size_t const id = op.input_ids[0];
    TensorType const &type = gc_.tensor_types()[id];
    Dtype const dtype = type.dtype();
    uint64_t const n = type.shape().size();
    std::string flat = values[id];
    if (type.shape().rank() != 1) {
        flat = hlo_append(
            std::format("{}[{}]", hlo_type(dtype), n),
            std::format("reshape({})", flat));
    }
    std::string const indices =
        hlo_append(std::format("s32[{}]", n), "iota(), iota_dimension=0");
    std::string const reduced = hlo_append(
        std::format("({}[], s32[])", hlo_type(dtype)),
        std::format(
            "reduce({}, {}, {}, {}), dimensions={{0}}, to_apply={}",
            flat,
            indices,
            hlo_constant(dtype, dtype_range(dtype).first),
            hlo_constant(Dtype::int32, 0),
            hlo_argmax_computation(dtype)));
    std::string const index = hlo_append(
        "s32[]", std::format("get-tuple-element({}), index=1", reduced));
    return dtype == Dtype::int32 ? index : hlo_convert(index, dtype, Shape{});
}

std::string
XlaCompiler::xla_op(ArgMinOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(ClipOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(MaxOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            return hlo_append(
                hlo_shape(type),
                std::format("maximum({}, {})", args[0], args[1]));
        });
}

std::string
XlaCompiler::xla_op(MinOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            return hlo_append(
                hlo_shape(type),
                std::format("minimum({}, {})", args[0], args[1]));
        });
}

// Products in the output's wider dtype, where they're exact, or for 64-bit
// inputs, wrapping in 64 bits. Those multiply as uint64, as XLA's algebraic
// simplifier takes a signed x * x to be nonnegative [XLA_LOWERING.md]
std::string
XlaCompiler::xla_op(MulOp const &op, std::vector<std::string> const &values)
{
    Dtype const input = gc_.tensor_types()[op.input_ids[0]].dtype();
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            Shape const &shape = type.shape();
            if (type.dtype() == Dtype::int64 && input == Dtype::int64) {
                std::string const unsigned_shape =
                    hlo_shape(Dtype::uint64, shape);
                std::string const a = hlo_append(
                    unsigned_shape,
                    std::format("bitcast-convert({})", args[0]));
                std::string const b = hlo_append(
                    unsigned_shape,
                    std::format("bitcast-convert({})", args[1]));
                std::string const product = hlo_append(
                    unsigned_shape, std::format("multiply({}, {})", a, b));
                return hlo_append(
                    hlo_shape(type),
                    std::format("bitcast-convert({})", product));
            }
            std::string const a =
                input == type.dtype()
                    ? args[0]
                    : hlo_convert(args[0], type.dtype(), shape);
            std::string const b =
                input == type.dtype()
                    ? args[1]
                    : hlo_convert(args[1], type.dtype(), shape);
            return hlo_append(
                hlo_shape(type), std::format("multiply({}, {})", a, b));
        });
}

// As the interpreter divides: in int64, where every dtype but uint64 fits and
// XLA's division truncates, as C++'s does, and gives INT64_MIN for INT64_MIN /
// -1, as the interpreter's wrapping negation does; and a uint64 by the
// denominator's magnitude, negated, wrapping, for a negative denominator.
// Validation rejected a denominator of 0
std::string
XlaCompiler::xla_op(DivOp const &op, std::vector<std::string> const &values)
{
    int64_t const denominator = op.params;
    size_t const id = op.input_ids[0];
    TensorType const &type = gc_.tensor_types()[id];
    Shape const &shape = type.shape();
    if (type.dtype() == Dtype::uint64) {
        uint64_t const magnitude =
            denominator < 0 ? uint64_t{0} - static_cast<uint64_t>(denominator)
                            : static_cast<uint64_t>(denominator);
        std::string quotient = hlo_append(
            hlo_shape(type),
            std::format(
                "divide({}, {})",
                values[id],
                hlo_splat(Dtype::uint64, magnitude, shape)));
        if (denominator > 0) {
            return quotient;
        }
        return hlo_append(
            hlo_shape(type),
            std::format(
                "subtract({}, {})",
                hlo_splat(Dtype::uint64, 0, shape),
                quotient));
    }
    bool const wide = type.dtype() == Dtype::int64;
    std::string const dividend =
        wide ? values[id] : hlo_convert(values[id], Dtype::int64, shape);
    std::string quotient = hlo_append(
        hlo_shape(Dtype::int64, shape),
        std::format(
            "divide({}, {})",
            dividend,
            hlo_splat(Dtype::int64, denominator, shape)));
    return wide ? quotient : hlo_convert(quotient, type.dtype(), shape);
}

std::string
XlaCompiler::xla_op(CastOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(ExpandOp const &op, std::vector<std::string> const &values)
{
    size_t const id = op.input_ids[0];
    return hlo_broadcast(values[id], gc_.tensor_types()[id], op.params);
}

std::string
XlaCompiler::xla_op(QMulOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(QDivOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(QMatMulOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string XlaCompiler::xla_op(
    ReduceSumOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string XlaCompiler::xla_op(
    ReduceMaxOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(QExpOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string XlaCompiler::xla_op(
    QInvSqrtOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(GatherOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

std::string
XlaCompiler::xla_op(ConcatOp const &op, std::vector<std::string> const &values)
{
    (void)op;
    (void)values; // TODO: fill in
    MONAD_ABORT();
}

// The module's entry computation takes the graph's inputs as its parameters,
// and returns its outputs as a tuple, one result each for NanoRt
Result<std::string> XlaCompiler::hlo_module()
{
    if (gc_.validation_result() != GraphEvalError::Success) {
        return gc_.validation_result();
    }

    // Read magic number
    BOOST_OUTCOME_TRY(read_next<uint16_t>(code_));

    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code_));
    std::vector<std::string> values;
    values.reserve(gc_.tensor_types().size());
    for (size_t id = 0; id < n_inputs; id++) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<TensorType>(code_));
        values.push_back(hlo_append(
            hlo_shape(gc_.tensor_types()[id]),
            std::format("parameter({})", id)));
    }

    BOOST_OUTCOME_TRY(read_next<uint8_t>(code_)); // n_outputs
    for (size_t i = 0; i < gc_.outputs().size(); i++) {
        // TODO: skip parsing the graph prelude
        BOOST_OUTCOME_TRY(read_next<uint16_t>(code_));
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code_));
    for (size_t i = 0; i < n_ops; i++) {
        BOOST_OUTCOME_TRY(
            visit_next(code_, [&]<typename OpT>(OpT const &op) -> Result<void> {
                if constexpr (std::same_as<OpT, TensorRefOp>) {
                    // Reads the state, which can fail
                    BOOST_OUTCOME_TRY(auto value, xla_op(op, values));
                    values.push_back(std::move(value));
                }
                else {
                    values.push_back(xla_op(op, values));
                }
                return outcome::success();
            }));
    }

    std::string shapes;
    std::string results;
    for (size_t i = 0; i < gc_.outputs().size(); i++) {
        size_t const id = gc_.outputs()[i];
        shapes += std::format(
            "{}{}", i == 0 ? "" : ", ", hlo_shape(gc_.tensor_types()[id]));
        results += std::format("{}{}", i == 0 ? "" : ", ", values[id]);
    }
    entry_ += std::format("  ROOT result = ({}) tuple({})\n", shapes, results);
    return std::format(
        "HloModule graph\n\n{}ENTRY main {{\n{}}}\n", computations_, entry_);
}

// Compiles the module for XLA_CPU. The library's parameter and result sizes
// are checked against the graph's tensors', which run() passes as they are
//
// TODO: compile asynchronously, in a child process, as XLA's CHECKs abort on
// a module they reject; and cache compiled graphs
Result<XlaCompiledGraph> XlaCompiler::compile(std::string *const ir)
{
    BOOST_OUTCOME_TRY(auto const hlo, hlo_module());
    monad_xla_options const options{XLA_CPU, XLA_FEATURES};
    monad_xla_executable *executable = nullptr;
    char *optimized = nullptr;
    char *error = nullptr;
    monad_xla_status const status = monad_xla_compile(
        hlo.data(),
        hlo.size(),
        &options,
        &executable,
        ir ? &optimized : nullptr,
        &error);
    if (ir) {
        *ir = std::format(
            "== input HLO ==\n{}\n== optimized HLO ==\n{}\n",
            hlo,
            optimized ? optimized : "");
        monad_xla_free(optimized);
    }
    if (status != MONAD_XLA_OK) {
        std::cerr << "XLA: " << (error ? error : "") << "\n" << hlo;
        monad_xla_free(error);
        return GraphEvalError::InternalError;
    }
    size_t const n_inputs = gc_.n_inputs();
    size_t const n_outputs = gc_.outputs().size();
    XlaCompiledGraph graph{executable, n_inputs, n_outputs};
    bool sizes_match = monad_xla_parameter_count(executable) == n_inputs &&
                       monad_xla_result_count(executable) == n_outputs;
    for (size_t i = 0; sizes_match && i < n_inputs; i++) {
        sizes_match = monad_xla_parameter_size(executable, i) ==
                      gc_.tensor_types()[i].size_bytes();
    }
    for (size_t i = 0; sizes_match && i < n_outputs; i++) {
        sizes_match = monad_xla_result_size(executable, i) ==
                      gc_.tensor_types()[gc_.outputs()[i]].size_bytes();
    }
    if (!sizes_match) {
        return GraphEvalError::InternalError;
    }
    return graph;
}

XlaCompiler::XlaCompiler(Graphcode const &gc, State &state)
    : gc_(gc)
    , code_(gc.code_span())
    , state_(state)
{
}

MONAD_GRAPH_EVAL_NAMESPACE_END
