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
#include <category/execution/monad/graph_eval/references.hpp>
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
#include <functional>
#include <iostream>
#include <map>
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

// u64 instructions for the fixed-point lowerings, on tensors of one shape:
// constants splatted to it, each made once, and the ops the lowerings use.
// Every multiply and left shift is unsigned, and so is every comparison, as
// the element type's default, as XLA_LOWERING.md's rules R1, R2 and R4 ask
class U64Builder
{
    std::function<std::string(std::string_view, std::string_view)> append_;
    std::function<std::string(uint64_t)> splat_;
    std::string shape_;
    std::string pred_shape_;
    std::map<uint64_t, std::string> constants_;

public:
    U64Builder(
        std::function<std::string(std::string_view, std::string_view)> append,
        std::function<std::string(uint64_t)> splat, Shape const &shape)
        : append_(std::move(append))
        , splat_(std::move(splat))
        , shape_(hlo_shape(Dtype::uint64, shape))
        , pred_shape_(hlo_pred_shape(shape))
    {
    }

    std::string constant(uint64_t const value)
    {
        auto const found = constants_.find(value);
        if (found != constants_.end()) {
            return found->second;
        }
        std::string name = splat_(value);
        constants_.emplace(value, name);
        return name;
    }

    std::string
    op(std::string_view const name, std::string const &a, std::string const &b)
    {
        return append_(shape_, std::format("{}({}, {})", name, a, b));
    }

    std::string clz(std::string const &x)
    {
        return append_(shape_, std::format("count-leading-zeros({})", x));
    }

    std::string compare(
        std::string const &a, std::string const &b,
        std::string_view const direction)
    {
        return append_(
            pred_shape_,
            std::format("compare({}, {}), direction={}", a, b, direction));
    }

    std::string logic(
        std::string_view const name, std::string const &a, std::string const &b)
    {
        return append_(pred_shape_, std::format("{}({}, {})", name, a, b));
    }

    std::string select(
        std::string const &condition, std::string const &yes,
        std::string const &no)
    {
        return append_(
            shape_, std::format("select({}, {}, {})", condition, yes, no));
    }
};

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

// Knuth's Algorithm D with 32-bit digits, as Hacker's Delight's divlu and
// compiler.cpp's mlir_divide_narrow: the divisor and the dividend are shifted
// until the divisor's top bit is set, and each quotient digit, estimated from
// the top digits, is corrected at most twice. The divisor must be nonzero.
// Every shift is by less than 64: the bits of `low` that shifting `high` moves
// in are (low >> 1) >> (63 - shift), none for a shift of 0
std::pair<std::string, std::string> XlaCompiler::hlo_divide_narrow(
    std::string const &high, std::string const &low, std::string const &divisor,
    Shape const &shape)
{
    U64Builder b{
        [&](std::string_view const s, std::string_view const i) {
            return hlo_append(s, i);
        },
        [&](uint64_t const value) {
            return hlo_splat(Dtype::uint64, value, shape);
        },
        shape};
    std::string const base = b.constant(uint64_t{1} << 32);
    std::string const mask = b.constant(0xffffffff);
    std::string const one = b.constant(1);
    std::string const thirty_two = b.constant(32);

    std::string const shift = b.clz(divisor);
    std::string const v = b.op("shift-left", divisor, shift);
    std::string const carried = b.op(
        "shift-right-logical",
        b.op("shift-right-logical", low, one),
        b.op("subtract", b.constant(63), shift));
    std::string const u32 =
        b.op("or", b.op("shift-left", high, shift), carried);
    std::string const u10 = b.op("shift-left", low, shift);
    std::string const v1 = b.op("shift-right-logical", v, thirty_two);
    std::string const v0 = b.op("and", v, mask);
    std::string const u1 = b.op("shift-right-logical", u10, thirty_two);
    std::string const u0 = b.op("and", u10, mask);

    auto const digit = [&](std::string const &dividend,
                           std::string const &next) {
        std::string q = b.op("divide", dividend, v1);
        std::string rhat = b.op("subtract", dividend, b.op("multiply", q, v1));
        auto const too_large = [&] {
            return b.logic(
                "or",
                b.compare(q, base, "GE"),
                b.compare(
                    b.op("multiply", q, v0),
                    b.op("or", b.op("shift-left", rhat, thirty_two), next),
                    "GT"));
        };
        std::string const first = too_large();
        q = b.select(first, b.op("subtract", q, one), q);
        rhat = b.select(first, b.op("add", rhat, v1), rhat);
        std::string const second = b.logic(
            "and",
            b.logic("and", first, b.compare(rhat, base, "LT")),
            too_large());
        return b.select(second, b.op("subtract", q, one), q);
    };

    std::string const q1 = digit(u32, u1);
    // What's left, below v, so computing it modulo 2^64 is exact
    std::string const u21 = b.op(
        "subtract",
        b.op("or", b.op("shift-left", u32, thirty_two), u1),
        b.op("multiply", q1, v));
    std::string const q0 = digit(u21, u0);
    std::string const quotient =
        b.op("or", b.op("shift-left", q1, thirty_two), q0);
    std::string const remainder = b.op(
        "shift-right-logical",
        b.op(
            "subtract",
            b.op("or", b.op("shift-left", u21, thirty_two), u0),
            b.op("multiply", q0, v)),
        shift);
    return {quotient, remainder};
}

// floor(sqrt(n)), integer only, as XLA_LOWERING.md's isqrt64: Newton's method
// from r = 2^ceil(width / 2), which is at least sqrt(n), each step
// r = min(r, (r + n / r) / 2). From r >= floor(sqrt(n)), a step never goes
// below it, and five reach it; the sixth is a margin. r + n / r can't
// overflow, as r is at most 2^32 and, while r >= sqrt(n), n / r is at most
// sqrt(n). For n = 0, r reaches 0, so each step divides by max(r, 1)
std::string XlaCompiler::hlo_isqrt64(std::string const &n, Shape const &shape)
{
    U64Builder b{
        [&](std::string_view const s, std::string_view const i) {
            return hlo_append(s, i);
        },
        [&](uint64_t const value) {
            return hlo_splat(Dtype::uint64, value, shape);
        },
        shape};
    std::string const one = b.constant(1);
    std::string const width = b.op("subtract", b.constant(64), b.clz(n));
    std::string r = b.op(
        "shift-left",
        one,
        b.op("shift-right-logical", b.op("add", width, one), one));
    for (int step = 0; step < 6; step++) {
        std::string const quotient = b.op("divide", n, b.op("maximum", r, one));
        r = b.op(
            "minimum",
            r,
            b.op("shift-right-logical", b.op("add", r, quotient), one));
    }
    return r;
}

std::string XlaCompiler::hlo_reduce_computation(
    std::string_view const name, Dtype const dtype)
{
    std::string computation = std::format("{}_{}", name, hlo_type(dtype));
    if (computation_names_.insert(computation).second) {
        computations_ += std::format(
            "{0} {{\n"
            "  {0}_a = {1}[] parameter(0)\n"
            "  {0}_b = {1}[] parameter(1)\n"
            "  ROOT {0}_r = {1}[] {2}({0}_a, {0}_b)\n"
            "}}\n\n",
            computation,
            hlo_type(dtype),
            name);
    }
    return computation;
}

// XLA_LOWERING.md section 7: a reduce over the axis, whose init must be the
// reducer's identity (rule R7), then a reshape that keeps the axis with
// length 1. An empty axis gives the init
std::string XlaCompiler::hlo_reduce_axis(
    size_t const id, uint8_t const axis, std::string_view const name,
    __int128 const init, std::vector<std::string> const &values)
{
    TensorType const &input = gc_.tensor_types()[id];
    TensorType const &type = gc_.tensor_types()[values.size()];
    Dtype const dtype = input.dtype();
    std::vector<uint16_t> kept;
    for (size_t i = 0; i < input.shape().rank(); i++) {
        if (i != axis) {
            kept.push_back(input.shape().dimensions()[i]);
        }
    }
    std::string const reduced = hlo_append(
        hlo_shape(hlo_type(dtype), kept),
        std::format(
            "reduce({}, {}), dimensions={{{}}}, to_apply={}",
            values[id],
            hlo_constant(dtype, init),
            axis,
            hlo_reduce_computation(name, dtype)));
    return hlo_append(hlo_shape(type), std::format("reshape({})", reduced));
}

// The low bits of a 64-bit value: reinterpreted as uint64, truncated to the
// unsigned dtype of `to`'s width, and reinterpreted as `to`, so that every
// conversion is modulo 2^w
std::string XlaCompiler::hlo_wrap64(
    std::string const &value, Dtype const from, Dtype const to,
    Shape const &shape)
{
    if (from == to) {
        return value;
    }
    auto const bitcast = [&](std::string const &x, Dtype const t) {
        return hlo_append(
            hlo_shape(t, shape), std::format("bitcast-convert({})", x));
    };
    std::string const bits =
        from == Dtype::uint64 ? value : bitcast(value, Dtype::uint64);
    if (to == Dtype::uint64) {
        return bits;
    }
    if (to == Dtype::int64) {
        return bitcast(bits, to);
    }
    if (!dtype_signed(to)) {
        return hlo_convert(bits, to, shape);
    }
    auto const same_width =
        static_cast<Dtype>(static_cast<uint8_t>(to) + 1); // The unsigned one
    return bitcast(hlo_convert(bits, same_width, shape), to);
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

// A constant, read from the account's code at lowering time, as
// XLA_LOWERING.md section 5 does: a compiled graph keeps the code it was
// compiled with
Result<std::string>
XlaCompiler::xla_op(TensorRefOp const &op, std::vector<std::string> const &)
{
    auto const &[type, address, offset] = op.params;
    std::vector<uint8_t> bytes(type.size_bytes());
    Tensor tensor{type, bytes.data()};
    BOOST_OUTCOME_TRY(load_code_tensor(
        state_, CodeRef{address, offset}, ByteOrder::LittleEndian, tensor));
    std::string elements;
    size_t index = 0;
    append_elements(elements, type, bytes, 0, index);
    return hlo_append(hlo_shape(type), std::format("constant({})", elements));
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

// A comparison, by the dtype's signedness, then 0 or 1 as uint8
std::string
XlaCompiler::xla_op(GeOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            std::string const compare = hlo_append(
                hlo_pred_shape(type.shape()),
                std::format("compare({}, {}), direction=GE", args[0], args[1]));
            return hlo_convert(compare, Dtype::uint8, type.shape());
        });
}

// A comparison, by the dtype's signedness, then 0 or 1 as uint8
std::string
XlaCompiler::xla_op(EqualOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            std::string const compare = hlo_append(
                hlo_pred_shape(type.shape()),
                std::format("compare({}, {}), direction=EQ", args[0], args[1]));
            return hlo_convert(compare, Dtype::uint8, type.shape());
        });
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

// q_mul: floor(a * b / 2^bits), wrapping to the dtype, as XLA_LOWERING.md
// section 11.2 lowers it. Up to 32 bits wide, the product is exact in 64
// bits, signed or not, and an arithmetic or logical shift floors it. A 64-bit
// product is on the u64 carrier (rule R2): its low word for 0 bits, else its
// 128 bits, from 32-bit halves, with the signed fix-up hi -= (a < 0 ? b : 0) +
// (b < 0 ? a : 0), and bits [bits, bits + 64) of it
std::string
XlaCompiler::xla_op(QMulOp const &op, std::vector<std::string> const &values)
{
    unsigned const bits = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = dtype_signed(dtype);
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            Shape const &shape = type.shape();
            if (dtype_size(dtype) <= 4) {
                Dtype const wide = sign ? Dtype::int64 : Dtype::uint64;
                std::string const product = hlo_append(
                    hlo_shape(wide, shape),
                    std::format(
                        "multiply({}, {})",
                        hlo_convert(args[0], wide, shape),
                        hlo_convert(args[1], wide, shape)));
                std::string const shifted =
                    bits == 0 ? product
                              : hlo_append(
                                    hlo_shape(wide, shape),
                                    std::format(
                                        "{}({}, {})",
                                        sign ? "shift-right-arithmetic"
                                             : "shift-right-logical",
                                        product,
                                        hlo_splat(wide, bits, shape)));
                return hlo_wrap64(shifted, wide, dtype, shape);
            }
            U64Builder b{
                [&](std::string_view const s, std::string_view const i) {
                    return hlo_append(s, i);
                },
                [&](uint64_t const value) {
                    return hlo_splat(Dtype::uint64, value, shape);
                },
                shape};
            std::string const u64_shape = hlo_shape(Dtype::uint64, shape);
            auto const carrier = [&](std::string const &x) {
                return sign ? hlo_append(
                                  u64_shape,
                                  std::format("bitcast-convert({})", x))
                            : x;
            };
            std::string const a = carrier(args[0]);
            std::string const c = carrier(args[1]);
            std::string const low = b.op("multiply", a, c);
            if (bits == 0) {
                return hlo_wrap64(low, Dtype::uint64, dtype, shape);
            }
            std::string const mask = b.constant(0xffffffff);
            std::string const thirty_two = b.constant(32);
            std::string const a0 = b.op("and", a, mask);
            std::string const a1 = b.op("shift-right-logical", a, thirty_two);
            std::string const c0 = b.op("and", c, mask);
            std::string const c1 = b.op("shift-right-logical", c, thirty_two);
            std::string const p00 = b.op("multiply", a0, c0);
            std::string const p01 = b.op("multiply", a0, c1);
            std::string const p10 = b.op("multiply", a1, c0);
            std::string const p11 = b.op("multiply", a1, c1);
            std::string const mid = b.op(
                "add",
                b.op(
                    "add",
                    b.op("shift-right-logical", p00, thirty_two),
                    b.op("and", p01, mask)),
                b.op("and", p10, mask));
            std::string high = b.op(
                "add",
                b.op(
                    "add",
                    b.op(
                        "add",
                        p11,
                        b.op("shift-right-logical", p01, thirty_two)),
                    b.op("shift-right-logical", p10, thirty_two)),
                b.op("shift-right-logical", mid, thirty_two));
            if (sign) {
                std::string const s64_zero = hlo_splat(Dtype::int64, 0, shape);
                auto const negative = [&](std::string const &x) {
                    return hlo_append(
                        hlo_pred_shape(shape),
                        std::format(
                            "compare({}, {}), direction=LT", x, s64_zero));
                };
                std::string const zero = b.constant(0);
                high = b.op(
                    "subtract",
                    high,
                    b.op(
                        "add",
                        b.select(negative(args[0]), c, zero),
                        b.select(negative(args[1]), a, zero)));
            }
            std::string const result = b.op(
                "or",
                b.op("shift-right-logical", low, b.constant(bits)),
                b.op("shift-left", high, b.constant(64 - bits)));
            return hlo_wrap64(result, Dtype::uint64, dtype, shape);
        });
}

// q_div: a * 2^bits / b, truncated toward zero and wrapping to the dtype, as
// fixed_point.hpp computes it, in two forms, as halide_compiler.cpp's:
// - when a * 2^bits fits 64 bits, with room left in a signed one for its
//   quotient by -1, a 64-bit division, which in XLA truncates toward zero;
// - otherwise compiler.cpp's long division of the magnitudes in 64-bit words,
//   as XLA_LOWERING.md section 11.3's wide path: |a| * 2^bits has a high and a
//   low word, and the wrapping keeps only the quotient's low word, which is
//   (high % |b|, low) / |b|, a division whose quotient fits 64 bits, by
//   hlo_divide_narrow. That is negated if the signs differ.
// Magnitudes are select(x < 0, 0 - x, x), never abs (rule R3).
//
// TODO: report a zero divisor, a DivisionByZero for the interpreter, as
// section 12's error flag would. Here it's replaced by 1, as in the other
// compilers, and the element is wrong
std::string
XlaCompiler::xla_op(QDivOp const &op, std::vector<std::string> const &values)
{
    unsigned const bits = op.params;
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    bool const sign = dtype_signed(dtype);
    unsigned const width = static_cast<unsigned>(8 * dtype_size(dtype));
    bool const narrow = sign ? width - 1 + bits <= 62 : width + bits <= 64;
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            Shape const &shape = type.shape();
            std::string const u64_shape = hlo_shape(Dtype::uint64, shape);
            std::string const s64_shape = hlo_shape(Dtype::int64, shape);
            Dtype const wide = sign ? Dtype::int64 : Dtype::uint64;
            auto const extend = [&](std::string const &x) {
                return dtype == wide ? x : hlo_convert(x, wide, shape);
            };
            auto const bitcast = [&](std::string const &x,
                                     std::string const &to) {
                return hlo_append(to, std::format("bitcast-convert({})", x));
            };
            auto const zero_to_one = [&](std::string const &x, Dtype const t) {
                std::string const zero = hlo_splat(t, 0, shape);
                std::string const is_zero = hlo_append(
                    hlo_pred_shape(shape),
                    std::format("compare({}, {}), direction=EQ", x, zero));
                return hlo_append(
                    hlo_shape(t, shape),
                    std::format(
                        "select({}, {}, {})",
                        is_zero,
                        hlo_splat(t, 1, shape),
                        x));
            };
            // The 64-bit result, wrapped to the dtype
            auto const narrowed = [&](std::string const &x, Dtype const from) {
                if (from == dtype) {
                    return x;
                }
                if (!sign) {
                    return hlo_convert(x, dtype, shape);
                }
                // To the unsigned dtype of the same width, then reinterpreted
                Dtype const same_width =
                    static_cast<Dtype>(static_cast<uint8_t>(dtype) + 1);
                std::string const as_unsigned =
                    from == Dtype::uint64 ? x : bitcast(x, u64_shape);
                if (dtype == Dtype::int64) {
                    return bitcast(as_unsigned, hlo_shape(type));
                }
                return bitcast(
                    hlo_convert(as_unsigned, same_width, shape),
                    hlo_shape(type));
            };

            if (narrow) {
                std::string dividend = extend(args[0]);
                if (bits != 0) {
                    std::string const carrier =
                        sign ? bitcast(dividend, u64_shape) : dividend;
                    std::string const shifted = hlo_append(
                        u64_shape,
                        std::format(
                            "shift-left({}, {})",
                            carrier,
                            hlo_splat(Dtype::uint64, bits, shape)));
                    dividend = sign ? bitcast(shifted, s64_shape) : shifted;
                }
                std::string const divisor = zero_to_one(extend(args[1]), wide);
                std::string const quotient = hlo_append(
                    hlo_shape(wide, shape),
                    std::format("divide({}, {})", dividend, divisor));
                return dtype == wide ? quotient
                                     : hlo_convert(quotient, dtype, shape);
            }

            U64Builder b{
                [&](std::string_view const s, std::string_view const i) {
                    return hlo_append(s, i);
                },
                [&](uint64_t const value) {
                    return hlo_splat(Dtype::uint64, value, shape);
                },
                shape};
            std::string const s64_zero = hlo_splat(Dtype::int64, 0, shape);
            // As unsigned: |INT64_MIN| is 2^63. And whether it's negative
            auto const magnitude = [&](std::string const &x) {
                std::string const extended = extend(x);
                if (!sign) {
                    return std::pair{extended, std::string{}};
                }
                std::string const bits64 = bitcast(extended, u64_shape);
                std::string const negative = hlo_append(
                    hlo_pred_shape(shape),
                    std::format(
                        "compare({}, {}), direction=LT", extended, s64_zero));
                return std::pair{
                    b.select(
                        negative,
                        b.op("subtract", b.constant(0), bits64),
                        bits64),
                    negative};
            };
            auto const [a, a_negative] = magnitude(args[0]);
            auto const [divisor_magnitude, b_negative] = magnitude(args[1]);
            std::string const divisor =
                zero_to_one(divisor_magnitude, Dtype::uint64);
            std::string const high =
                bits == 0
                    ? b.constant(0)
                    : b.op("shift-right-logical", a, b.constant(64 - bits));
            std::string const low =
                bits == 0 ? a : b.op("shift-left", a, b.constant(bits));
            std::string quotient =
                hlo_divide_narrow(
                    b.op("remainder", high, divisor), low, divisor, shape)
                    .first;
            if (sign) {
                quotient = b.select(
                    b.logic("xor", a_negative, b_negative),
                    b.op("subtract", b.constant(0), quotient),
                    quotient);
            }
            return narrowed(quotient, Dtype::uint64);
        });
}

// q_matmul, as XLA_LOWERING.md section 8.3 lowers it when one 64-bit dot is
// exact: for inputs up to 16 bits wide, whose sums are exact in 64 bits, and
// when `bits` plus the output's width is at most 64, as only the sums' low 64
// bits reach the output. Both operands extended to int64 or uint64, by the
// input's signedness, one dot, which XLA:CPU runs as a wrapping LLVM IR loop
// for 64-bit types (rule R6), a shift by `bits`, then the low bits, as the
// output's dtype.
//
// TODO: the other cases, whose sums need 128 bits: section 8.3's one-sided
// split for 32-bit inputs and 22-bit limbs for 64-bit ones
std::string
XlaCompiler::xla_op(QMatMulOp const &op, std::vector<std::string> const &values)
{
    auto const [bits, out_dtype] = op.params;
    TensorType const &x = gc_.tensor_types()[op.input_ids[0]];
    TensorType const &y = gc_.tensor_types()[op.input_ids[1]];
    TensorType const &type = gc_.tensor_types()[values.size()];
    Dtype const dtype = x.dtype();
    bool const sign = dtype_signed(dtype);
    if (dtype_size(dtype) > 2 && bits + 8 * dtype_size(out_dtype) > 64) {
        MONAD_ABORT();
    }
    Dtype const wide = sign ? Dtype::int64 : Dtype::uint64;
    auto const extend = [&](size_t const id, TensorType const &t) {
        return dtype == wide ? values[id]
                             : hlo_convert(values[id], wide, t.shape());
    };
    Shape const &shape = type.shape();
    std::string const sums = hlo_append(
        hlo_shape(wide, shape),
        std::format(
            "dot({}, {}), lhs_contracting_dims={{1}}, "
            "rhs_contracting_dims={{0}}",
            extend(op.input_ids[0], x),
            extend(op.input_ids[1], y)));
    std::string const shifted =
        bits == 0
            ? sums
            : hlo_append(
                  hlo_shape(wide, shape),
                  std::format(
                      "{}({}, {})",
                      sign ? "shift-right-arithmetic" : "shift-right-logical",
                      sums,
                      hlo_splat(wide, bits, shape)));
    return hlo_wrap64(shifted, wide, out_dtype, shape);
}

std::string XlaCompiler::xla_op(
    ReduceSumOp const &op, std::vector<std::string> const &values)
{
    return hlo_reduce_axis(op.input_ids[0], op.params, "add", 0, values);
}

std::string XlaCompiler::xla_op(
    ReduceMaxOp const &op, std::vector<std::string> const &values)
{
    Dtype const dtype = gc_.tensor_types()[op.input_ids[0]].dtype();
    return hlo_reduce_axis(
        op.input_ids[0],
        op.params,
        "maximum",
        dtype_range(dtype).first,
        values);
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

// numpy's take along the axis, as XLA_LOWERING.md section 10 lowers it: each
// index a slice of the data with 1 along the axis, collapsed, so the output's
// dimensions are the data's before the axis, the indices', then the data's
// after it. The indices keep their dtype.
//
// TODO: report an index out of range, an IndexError for the interpreter, as
// section 12's error flag would. XLA clamps it, and the element is wrong. An
// empty axis has nothing to read: its elements are 0
std::string
XlaCompiler::xla_op(GatherOp const &op, std::vector<std::string> const &values)
{
    size_t const axis = op.params;
    TensorType const &data = gc_.tensor_types()[op.input_ids[0]];
    TensorType const &indices = gc_.tensor_types()[op.input_ids[1]];
    TensorType const &type = gc_.tensor_types()[values.size()];
    size_t const rank = data.shape().rank();
    size_t const index_rank = indices.shape().rank();
    if (data.shape().dimensions()[axis] == 0) {
        return hlo_splat(type.dtype(), 0, type.shape());
    }
    auto const list = [](std::vector<size_t> const &xs) {
        std::string text;
        for (size_t const x : xs) {
            text += std::format("{}{}", text.empty() ? "" : ",", x);
        }
        return text;
    };
    std::vector<size_t> offset_dims;
    for (size_t i = 0; i < axis; i++) {
        offset_dims.push_back(i);
    }
    for (size_t i = axis + index_rank; i + 1 < rank + index_rank; i++) {
        offset_dims.push_back(i);
    }
    std::vector<size_t> slice_sizes;
    for (size_t i = 0; i < rank; i++) {
        slice_sizes.push_back(i == axis ? 1 : data.shape().dimensions()[i]);
    }
    return hlo_append(
        hlo_shape(type),
        std::format(
            "gather({}, {}), offset_dims={{{}}}, collapsed_slice_dims={{{}}}, "
            "start_index_map={{{}}}, index_vector_dim={}, slice_sizes={{{}}}",
            values[op.input_ids[0]],
            values[op.input_ids[1]],
            list(offset_dims),
            axis,
            axis,
            index_rank,
            list(slice_sizes)));
}

std::string
XlaCompiler::xla_op(ConcatOp const &op, std::vector<std::string> const &values)
{
    TensorType const &type = gc_.tensor_types()[values.size()];
    return hlo_append(
        hlo_shape(type),
        std::format(
            "concatenate({}, {}), dimensions={{{}}}",
            values[op.input_ids[0]],
            values[op.input_ids[1]],
            op.params));
}

// floor(sqrt(x)), for an unsigned x, by hlo_isqrt64 on its 64-bit extension;
// the root of a w-bit value fits w bits
std::string
XlaCompiler::xla_op(ISqrtOp const &op, std::vector<std::string> const &values)
{
    return hlo_elementwise(
        op.input_ids, values, [&](auto const &args, TensorType const &type) {
            Shape const &shape = type.shape();
            bool const wide = type.dtype() == Dtype::uint64;
            std::string const n =
                wide ? args[0] : hlo_convert(args[0], Dtype::uint64, shape);
            std::string const root = hlo_isqrt64(n, shape);
            return wide ? root : hlo_convert(root, type.dtype(), shape);
        });
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
