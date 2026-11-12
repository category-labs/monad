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
#include <category/core/math.hpp>
#include <category/execution/monad/graph_eval/broadcasting.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/fuse_interpreted.hpp>
#include <category/execution/monad/graph_eval/fuse_kernels.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/matmul.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <concepts>
#include <cstdint>
#include <cstring>
#include <functional>
#include <initializer_list>
#include <memory>
#include <optional>
#include <type_traits>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// A field of the code, which can be at any alignment
template <typename T>
T load(uint8_t const *const p)
{
    T value;
    std::memcpy(&value, p, sizeof(T));
    return value;
}

template <typename F, typename T>
using out_t = std::conditional_t<
    std::same_as<std::invoke_result_t<F, T, T>, bool>, uint8_t,
    std::invoke_result_t<F, T, T>>;

// The kernels are fuse_claude's steps, given their operands' chunks directly

using fuse_kernels::broadcast_chunk;
using fuse_kernels::gather_type;
using fuse_kernels::Instruction;
using fuse_kernels::matrix;

// Adds part of a row to the running sums, which are also the results. The
// restrict pointers let GCC vectorize the loops without checking for overlap,
// which it doesn't do at -O2
template <typename T>
[[gnu::always_inline]]
inline void add_row(
    T const *__restrict const xs, T *__restrict const sums,
    T *__restrict const outs, uint64_t const length, bool const first_row)
{
    if (first_row) {
        for (uint64_t i = 0; i < length; i++) {
            sums[i] = xs[i];
            outs[i] = xs[i];
        }
    }
    else {
        for (uint64_t i = 0; i < length; i++) {
            T const sum = WrappingAdd{}(sums[i], xs[i]);
            sums[i] = sum;
            outs[i] = sum;
        }
    }
}

// The chunks come in order, so each element's running sum is the one above it
// in the previous row, which is kept in the row of sums from chunk to chunk
template <typename T>
void cumsum_chunk(
    T const *const xs, T *const sums, T *const outs, uint64_t const start,
    uint64_t const length, uint64_t const inner, uint64_t const rows)
{
    uint64_t column = start % inner;
    uint64_t row = start / inner % rows;
    for (uint64_t i = 0; i < length;) {
        uint64_t const run = std::min(inner - column, length - i);
        add_row(xs + i, sums + column, outs + i, run, row == 0);
        i += run;
        column += run;
        if (column == inner) {
            column = 0;
            row = row + 1 == rows ? 0 : row + 1;
        }
    }
}

// The chunk's rows of the product, from the same rows of x and all of y. A
// matrix times a vector is a dot product a row, as in the lite compiler
void matmul_chunk(
    int8_t *const x, int8_t *const y, int32_t *const outs, uint64_t const start,
    uint64_t const length, uint64_t const inner, uint64_t const columns)
{
    uint64_t const first_row = start / columns;
    uint64_t const rows = length / columns;
    int8_t *const xs = x + first_row * inner;
    if (columns == 1) {
        for (uint64_t row = 0; row < rows; row++) {
            // Can't overflow: at most 65535 products of magnitude 2^14
            int32_t sum = 0;
            for (uint64_t i = 0; i < inner; i++) {
                sum += int32_t{xs[row * inner + i]} * int32_t{y[i]};
            }
            outs[row] = sum;
        }
        return;
    }
    Tensor out = matrix(Dtype::int32, rows, columns, outs);
    matmul_i8(
        matrix(Dtype::int8, rows, inner, xs),
        matrix(Dtype::int8, inner, columns, y),
        out);
}

// A MatMulEager's whole product, as the MatMul op computes it: a matrix times
// a vector a dot product a row, with matvec_i8, else with matmul_i8
void matmul_eager(
    int8_t *const x, int8_t *const y, int32_t *const out, uint64_t const rows,
    uint64_t const inner, uint64_t const columns)
{
    if (columns == 1) {
        matvec_i8(x, y, out, rows, inner);
        return;
    }
    Tensor product = matrix(Dtype::int32, rows, columns, out);
    matmul_i8(
        matrix(Dtype::int8, rows, inner, x),
        matrix(Dtype::int8, inner, columns, y),
        product);
}

// The whole input's ArgMax, as the result has a single element
template <typename T>
void argmax_chunk(T const *const xs, T *const out, uint64_t const inner)
{
    uint64_t largest = 0;
    for (uint64_t i = 1; i < inner; i++) {
        if (xs[largest] < xs[i]) {
            largest = i;
        }
    }
    *out = static_cast<T>(largest);
}

template <typename T>
void div_chunk(
    T const *const xs, T *const outs, uint64_t const length, bool const stride,
    int64_t const denominator)
{
    auto const divide = [denominator](T const x) -> T {
        if constexpr (std::same_as<T, uint64_t>) {
            // x / |denominator| always fits, and negating it wraps
            uint64_t const magnitude =
                denominator < 0
                    ? uint64_t{0} - static_cast<uint64_t>(denominator)
                    : static_cast<uint64_t>(denominator);
            uint64_t const quotient = x / magnitude;
            return denominator < 0 ? uint64_t{0} - quotient : quotient;
        }
        else if (denominator == -1) {
            // INT64_MIN / -1 overflows, so negate with wrapping instead
            return static_cast<T>(
                uint64_t{0} - static_cast<uint64_t>(static_cast<int64_t>(x)));
        }
        else {
            return static_cast<T>(static_cast<int64_t>(x) / denominator);
        }
    };
    run_op1<decltype(divide)>(xs, outs, length, stride, divide);
}

// Division by 2^shift, rounding toward zero as Div does
template <typename T>
void div_pow2_chunk(
    T const *const xs, T *const outs, uint64_t const length, bool const stride,
    unsigned const shift)
{
    // Every quotient is 0, and shifting by the type's width is undefined
    if (shift >= 8 * sizeof(T)) {
        std::fill_n(outs, length, T{0});
        return;
    }
    if constexpr (std::is_signed_v<T>) {
        // Adding 2^shift - 1 to negative values rounds toward zero
        auto const divide = [shift,
                             mask = static_cast<T>((uint64_t{1} << shift) - 1)](
                                T const x) -> T {
            return static_cast<T>((x < 0 ? x + mask : x) >> shift);
        };
        run_op1<decltype(divide)>(xs, outs, length, stride, divide);
    }
    else {
        auto const divide = [shift](T const x) -> T {
            return static_cast<T>(x >> shift);
        };
        run_op1<decltype(divide)>(xs, outs, length, stride, divide);
    }
}

// A binary instruction's result's dtype, for operands of `dtype`
Dtype binary_dtype(FusedInstruction const opcode, Dtype const dtype)
{
    switch (opcode) {
    case FusedInstruction::Mul:
        return widened_dtype(dtype);
    case FusedInstruction::Greater:
    case FusedInstruction::Ge:
    case FusedInstruction::Equal:
        return Dtype::uint8;
    default:
        return dtype;
    }
}

// An instruction's broadcast loops, constructed only for an Input or Gather
// that's broadcast: BroadcastLoops' Shape zero-fills itself on construction,
// which for every instruction of every op cost more than many ops' work
union LoopsSlot
{
    LoopsSlot() {}

    BroadcastLoops<2> loops;
};

// A value on the stack: its chunk's elements, contiguous or one repeated, and
// the chunk buffer it's in, if any
struct Value
{
    Dtype dtype;
    uint8_t *data;
    bool stride;
    int32_t slot;
};

void run_binary(
    FusedInstruction const opcode, Value const &x, Value const &y,
    uint8_t *const out, uint64_t const length)
{
    visit_dtype(x.dtype, [&]<typename T>() {
        auto const run = [&]<typename F>() {
            run_op2<F>(
                reinterpret_cast<T const *>(x.data),
                reinterpret_cast<T const *>(y.data),
                reinterpret_cast<out_t<F, T> *>(out),
                length,
                x.stride,
                y.stride);
        };
        switch (opcode) {
        case FusedInstruction::Add:
            run.template operator()<WrappingAdd>();
            break;
        case FusedInstruction::Sub:
            run.template operator()<WrappingSub>();
            break;
        case FusedInstruction::Mul:
            run.template operator()<WideningMul>();
            break;
        case FusedInstruction::Max:
            run.template operator()<Maximum>();
            break;
        case FusedInstruction::Min:
            run.template operator()<Minimum>();
            break;
        case FusedInstruction::Greater:
            run.template operator()<std::greater<>>();
            break;
        case FusedInstruction::Ge:
            run.template operator()<std::greater_equal<>>();
            break;
        case FusedInstruction::Equal:
            run.template operator()<std::equal_to<>>();
            break;
        default:
            MONAD_ABORT();
        }
    });
}

// An op's chunk buffers, given out as FusedGraphCompiler's planning gives
// them: the one freed last, if any, else a new one. At most one per
// instruction, and one for the core
struct Slots
{
    uint8_t *base;
    uint64_t bytes;
    uint32_t n = 0;
    std::array<uint32_t, MAX_FUSED_INSTRUCTIONS + 1> free{};
    size_t n_free = 0;

    uint32_t next()
    {
        return n_free == 0 ? n++ : free[--n_free];
    }

    void release(Value const &value)
    {
        if (value.slot >= 0) {
            free[n_free++] = static_cast<uint32_t>(value.slot);
        }
    }
};

// What validation keeps of a value on the stack while it plans the chunk
// buffers, as FusedGraphCompiler's planning does
struct Planned
{
    Dtype dtype;
    std::optional<uint32_t> slot;
};

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// FusedGraphCompiler's reading of the code, with its checks, and its planning
// of each op's chunk buffers, for the memory's size, but with no steps
class FusedInterpreter::Validator
{
    std::span<uint8_t const> code_;
    FusedInterpreter &interpreter_;
    std::vector<size_t> outputs_;
    uint64_t region_size_ = 0;

    Result<uint32_t> allocate(TensorType const &type);
    Result<void> read_op();

public:
    Validator(
        std::span<uint8_t const> const code, FusedInterpreter &interpreter)
        : code_(code)
        , interpreter_(interpreter)
    {
    }

    Result<void> read_code();
};

Result<uint32_t> FusedInterpreter::Validator::allocate(TensorType const &type)
{
    uint64_t const offset = interpreter_.tensors_size_;
    if (type.size_bytes() > ARENA_SIZE - offset) {
        return GraphEvalError::OutOfMemory;
    }
    interpreter_.tensors_size_ =
        round_up<uint64_t>(offset + type.size_bytes(), TENSOR_DATA_ALIGNMENT);
    return static_cast<uint32_t>(offset);
}

Result<void> FusedInterpreter::Validator::read_code()
{
    BOOST_OUTCOME_TRY(auto const magic, read_next<uint16_t>(code_));
    if (MONAD_UNLIKELY(magic != FUSED_MAGIC)) {
        return GraphEvalError::GraphValidationError;
    }

    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code_));
    if (n_inputs > MAX_GRAPH_INPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t i = 0; i < n_inputs; i++) {
        BOOST_OUTCOME_TRY(auto const type, read_next<TensorType>(code_));
        BOOST_OUTCOME_TRY(auto const offset, allocate(type));
        interpreter_.node_types_.push_back(type);
        interpreter_.node_offsets_.push_back(offset);
        interpreter_.product_offsets_.push_back(0);
        interpreter_.input_offsets_.push_back(offset);
    }

    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(code_));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(auto const output_id, read_next<uint16_t>(code_));
        outputs_.push_back(output_id);
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code_));
    interpreter_.ops_offset_ = interpreter_.code_.size() - code_.size();
    interpreter_.n_ops_ = n_ops;
    for (size_t i = 0; i < n_ops; i++) {
        BOOST_OUTCOME_TRY(read_op());
    }
    if (!code_.empty()) {
        return GraphEvalError::GraphValidationError;
    }

    for (size_t const id : outputs_) {
        if (id >= interpreter_.node_offsets_.size()) {
            return GraphEvalError::GraphValidationError;
        }
        interpreter_.output_offsets_.push_back(interpreter_.node_offsets_[id]);
    }
    interpreter_.memory_size_ = interpreter_.tensors_size_ + region_size_;
    if (interpreter_.memory_size_ > ARENA_SIZE) {
        return GraphEvalError::OutOfMemory;
    }
    return outcome::success();
}

Result<void> FusedInterpreter::Validator::read_op()
{
    auto &node_types = interpreter_.node_types_;
    auto &node_offsets = interpreter_.node_offsets_;
    BOOST_OUTCOME_TRY(
        auto const op_core, fuse_kernels::read_core(code_, node_types));
    FusedCore const core = op_core.core;
    auto const &core_inputs = op_core.inputs;
    auto const &core_type = op_core.type;
    uint8_t const axis = op_core.axis;
    BOOST_OUTCOME_TRY(
        auto const instructions,
        fuse_kernels::read_instructions(
            code_, node_types.size(), core != FusedCore::Map));
    if (core == FusedCore::Reshape) {
        if (!instructions.empty()) {
            return GraphEvalError::GraphValidationError;
        }
        uint32_t const offset = node_offsets[core_inputs[0]];
        node_types.push_back(*core_type);
        node_offsets.push_back(offset);
        interpreter_.product_offsets_.push_back(0);
        return outcome::success();
    }

    // The shapes the result's is broadcast from: the core's, then the Inputs'
    std::vector<Shape> shapes;
    if (core_type) {
        shapes.push_back(core_type->shape());
    }
    for (Instruction const &instruction : instructions) {
        if (instruction.opcode == FusedInstruction::Input) {
            shapes.push_back(node_types[instruction.input_id].shape());
        }
        if (instruction.opcode == FusedInstruction::Gather) {
            BOOST_OUTCOME_TRY(
                auto const type, gather_type(node_types, instruction));
            shapes.push_back(type.shape());
        }
    }
    BOOST_OUTCOME_TRY(auto const shape, broadcast_shape(shapes));
    if (core_type && shape != shapes[0]) {
        return GraphEvalError::ShapeError;
    }
    uint64_t const size = shape.size();

    uint64_t chunk = FUSED_CHUNK;
    if (core == FusedCore::MatMul || core == FusedCore::QMatMul) {
        uint64_t const columns = std::max<uint64_t>(shape.dimensions()[1], 1);
        chunk = std::max<uint64_t>(FUSED_CHUNK / columns, 1) * columns;
    }
    uint64_t const slot_bytes = chunk * sizeof(uint64_t);
    uint64_t slots_offset = 0;
    uint32_t n_slots = 0;
    std::vector<uint32_t> free_slots;
    std::vector<Planned> stack;
    auto const next_value = [&](Dtype const dtype) {
        uint32_t slot = n_slots;
        if (free_slots.empty()) {
            n_slots++;
        }
        else {
            slot = free_slots.back();
            free_slots.pop_back();
        }
        return Planned{dtype, slot};
    };
    auto const pop = [&]() -> Result<Planned> {
        if (stack.empty()) {
            return GraphEvalError::GraphValidationError;
        }
        Planned const value = stack.back();
        stack.pop_back();
        return value;
    };
    auto const push_step = [&](Dtype const dtype,
                               std::initializer_list<Planned> const inputs) {
        Planned const value = next_value(dtype);
        for (Planned const &input : inputs) {
            if (input.slot) {
                free_slots.push_back(*input.slot);
            }
        }
        stack.push_back(value);
    };

    std::optional<Planned> core_value;
    uint32_t product_offset = 0;
    if (core_type) {
        Dtype const dtype = core_type->dtype();
        if (core == FusedCore::CumSum) {
            uint64_t inner = 1;
            for (size_t i = axis + 1u; i < shape.rank(); i++) {
                inner *= shape.dimensions()[i];
            }
            // The row of running sums goes before the chunk buffers
            slots_offset = round_up<uint64_t>(
                inner * dtype_size(dtype), TENSOR_DATA_ALIGNMENT);
        }
        if (is_whole_core(core)) {
            BOOST_OUTCOME_TRY(product_offset, allocate(*core_type));
            core_value = Planned{dtype, std::nullopt};
        }
        else {
            core_value = next_value(dtype);
            // Core can be pushed any number of times, so its buffer stays
            // taken
            core_value->slot.reset();
        }
    }

    for (Instruction const &instruction : instructions) {
        switch (instruction.opcode) {
        case FusedInstruction::Core:
            stack.push_back(*core_value);
            break;
        case FusedInstruction::Input: {
            TensorType const &type = node_types[instruction.input_id];
            uint64_t const n = type.shape().size();
            if (n == size || n == 1) {
                stack.push_back(Planned{type.dtype(), std::nullopt});
                break;
            }
            BOOST_OUTCOME_TRY(broadcast<2>({shape, type.shape()}));
            stack.push_back(next_value(type.dtype()));
            break;
        }
        case FusedInstruction::Constant:
            stack.push_back(Planned{instruction.dtype, std::nullopt});
            break;
        case FusedInstruction::Gather: {
            BOOST_OUTCOME_TRY(
                auto const type, gather_type(node_types, instruction));
            BOOST_OUTCOME_TRY(broadcast<2>({shape, type.shape()}));
            stack.push_back(next_value(type.dtype()));
            break;
        }
        case FusedInstruction::QMul:
        case FusedInstruction::QDiv: {
            BOOST_OUTCOME_TRY(auto const y, pop());
            BOOST_OUTCOME_TRY(auto const x, pop());
            if (x.dtype != y.dtype) {
                return GraphEvalError::TypeError;
            }
            push_step(x.dtype, {x, y});
            break;
        }
        case FusedInstruction::QExp:
        case FusedInstruction::QInvSqrt: {
            BOOST_OUTCOME_TRY(auto const x, pop());
            push_step(x.dtype, {x});
            break;
        }
        case FusedInstruction::ISqrt: {
            BOOST_OUTCOME_TRY(auto const x, pop());
            if (dtype_signed(x.dtype)) {
                return GraphEvalError::TypeError;
            }
            push_step(x.dtype, {x});
            break;
        }
        case FusedInstruction::Sub:
        case FusedInstruction::Greater:
        case FusedInstruction::Ge:
        case FusedInstruction::Equal:
        case FusedInstruction::Add:
        case FusedInstruction::Mul:
        case FusedInstruction::Max:
        case FusedInstruction::Min: {
            BOOST_OUTCOME_TRY(auto const y, pop());
            BOOST_OUTCOME_TRY(auto const x, pop());
            if (x.dtype != y.dtype) {
                return GraphEvalError::TypeError;
            }
            push_step(binary_dtype(instruction.opcode, x.dtype), {x, y});
            break;
        }
        case FusedInstruction::Div: {
            BOOST_OUTCOME_TRY(auto const x, pop());
            push_step(x.dtype, {x});
            break;
        }
        case FusedInstruction::Saturate: {
            BOOST_OUTCOME_TRY(auto const x, pop());
            push_step(instruction.dtype, {x});
            break;
        }
        case FusedInstruction::Where: {
            BOOST_OUTCOME_TRY(auto const y, pop());
            BOOST_OUTCOME_TRY(auto const x, pop());
            BOOST_OUTCOME_TRY(auto const condition, pop());
            if (condition.dtype != Dtype::uint8 || x.dtype != y.dtype) {
                return GraphEvalError::TypeError;
            }
            push_step(x.dtype, {condition, x, y});
            break;
        }
        }
    }
    if (stack.size() != 1) {
        return GraphEvalError::GraphValidationError;
    }

    BOOST_OUTCOME_TRY(
        auto const type, TensorType::checked(stack.back().dtype, shape));
    BOOST_OUTCOME_TRY(auto const offset, allocate(type));
    node_types.push_back(type);
    node_offsets.push_back(offset);
    interpreter_.product_offsets_.push_back(product_offset);
    region_size_ =
        std::max(region_size_, slots_offset + uint64_t{n_slots} * slot_bytes);
    return outcome::success();
}

Result<FusedInterpreter>
FusedInterpreter::validate(std::span<uint8_t const> const code)
{
    FusedInterpreter interpreter;
    interpreter.code_ = code;
    BOOST_OUTCOME_TRY(Validator(code, interpreter).read_code());
    return interpreter;
}

Result<void>
FusedInterpreter::run(std::span<uint8_t> const memory, State *const state) const
{
    MONAD_ASSERT(memory.size() >= memory_size_);
    std::span<uint8_t const> code = code_.subspan(ops_offset_);
    size_t node = input_offsets_.size();
    for (size_t i = 0; i < n_ops_; i++) {
        GraphEvalError const error = run_op(code, node++, memory.data(), state);
        if (error != GraphEvalError::Success) {
            return GraphEvalError{error};
        }
    }
    return outcome::success();
}

// Reads the op's core and finds its instructions, then for each chunk runs
// the core, and walks the instructions as a stack program, each one's kernel
// writing its chunk to a chunk buffer, or, for the last, to the op's result.
// Returns the first error of a core or an instruction
GraphEvalError FusedInterpreter::run_op(
    std::span<uint8_t const> &code, size_t const node, uint8_t *const memory,
    State *const state) const
{
    uint8_t const *p = code.data();
    auto const core = static_cast<FusedCore>(*p++);
    std::array<size_t, 2> ids{};
    uint8_t axis = 0;
    // The type of a Literal, a TensorRef, a CumSumEager, ArgMaxEager,
    // ReduceSumEager or ReduceMaxEager, or a Gather core, set below; a
    // Literal's elements, a TensorRef's tensor, a QMatMul's bits and result
    // dtype
    TensorType core_type{};
    uint8_t const *literal = nullptr;
    CodeRef ref{};
    unsigned bits = 0;
    Dtype out_dtype = Dtype::int8;
    switch (core) {
    case FusedCore::Map:
        break;
    case FusedCore::Literal: {
        std::span<uint8_t const> rest = code.subspan(1);
        auto const [type, elements] =
            read_next<std::tuple<TensorType, std::span<uint8_t const>>>(rest)
                .value();
        core_type = type;
        literal = elements.data();
        p = rest.data();
        break;
    }
    case FusedCore::TensorRef: {
        std::span<uint8_t const> rest = code.subspan(1);
        auto const [type, address, offset] =
            read_next<std::tuple<TensorType, Address, uint32_t>>(rest).value();
        core_type = type;
        ref = CodeRef{address, offset};
        p = rest.data();
        break;
    }
    case FusedCore::QMatMul:
    case FusedCore::QMatMulEager:
        bits = *p++;
        out_dtype = static_cast<Dtype>(*p++);
        ids[0] = load<uint16_t>(p);
        ids[1] = load<uint16_t>(p + 2);
        p += 4;
        break;
    case FusedCore::CumSum:
    case FusedCore::ReduceSum:
    case FusedCore::ReduceMax:
    case FusedCore::CumSumEager:
    case FusedCore::ReduceSumEager:
    case FusedCore::ReduceMaxEager:
        axis = *p++;
        ids[0] = load<uint16_t>(p);
        p += 2;
        break;
    case FusedCore::Concat:
    case FusedCore::Gather:
        axis = *p++;
        ids[0] = load<uint16_t>(p);
        ids[1] = load<uint16_t>(p + 2);
        p += 4;
        break;
    case FusedCore::MatMul:
    case FusedCore::MatMulEager:
        ids[0] = load<uint16_t>(p);
        ids[1] = load<uint16_t>(p + 2);
        p += 4;
        break;
    case FusedCore::ArgMax:
    case FusedCore::ArgMaxEager:
        ids[0] = load<uint16_t>(p);
        p += 2;
        break;
    case FusedCore::Reshape: {
        uint8_t const rank = *p++;
        p += 2 * size_t{rank};
        ids[0] = load<uint16_t>(p);
        p += 2;
        break;
    }
    }
    size_t const n_instructions = *p++;
    uint8_t const *const program = p;

    // The op's end, past its instructions; the broadcast loops of the Inputs
    // and Gathers read through them; and each Constant's element, at the start
    // of a uint64_t of its own, read once for all the chunks
    TensorType const &type = node_types_[node];
    Shape const &shape = type.shape();
    uint64_t const size = shape.size();
    std::array<LoopsSlot, MAX_FUSED_INSTRUCTIONS> loops;
    std::array<uint64_t, MAX_FUSED_INSTRUCTIONS> constants;
    for (size_t i = 0; i < n_instructions; i++) {
        auto const opcode = static_cast<FusedInstruction>(*p++);
        switch (opcode) {
        case FusedInstruction::Input: {
            Shape const &input = node_types_[load<uint16_t>(p)].shape();
            p += 2;
            if (input.size() != size && input.size() != 1) {
                std::construct_at(
                    &loops[i].loops, broadcast<2>({shape, input}).value());
            }
            break;
        }
        case FusedInstruction::Gather: {
            GatherOp op{};
            op.params = p[4];
            TensorType const gathered =
                op.check_impl({&node_types_[load<uint16_t>(p)],
                               &node_types_[load<uint16_t>(p + 2)]})
                    .value();
            p += 5;
            std::construct_at(
                &loops[i].loops,
                broadcast<2>({shape, gathered.shape()}).value());
            break;
        }
        case FusedInstruction::Constant: {
            auto const dtype = static_cast<Dtype>(*p++);
            constants[i] = 0;
            std::memcpy(&constants[i], p, dtype_size(dtype));
            p += dtype_size(dtype);
            break;
        }
        case FusedInstruction::Div:
            p += sizeof(int64_t);
            break;
        case FusedInstruction::Saturate:
            p += 1;
            break;
        default:
            if (has_fractional_bits(opcode)) {
                p += 1;
            }
            break;
        }
    }
    code = code.subspan(static_cast<size_t>(p - code.data()));
    if (core == FusedCore::Reshape) {
        return GraphEvalError::Success;
    }

    uint64_t chunk = FUSED_CHUNK;
    uint64_t inner = 0;
    uint64_t rows = 0;
    uint64_t columns = 0;
    uint64_t slots_offset = 0;
    Dtype core_dtype = type.dtype();
    auto const input = [&](size_t const i) -> TensorType const & {
        return node_types_[ids[i]];
    };
    switch (core) {
    case FusedCore::CumSum:
        inner = dimensions_product(shape, axis + 1u, shape.rank());
        rows = shape.dimensions()[axis];
        core_dtype = input(0).dtype();
        slots_offset = round_up<uint64_t>(
            inner * dtype_size(core_dtype), TENSOR_DATA_ALIGNMENT);
        break;
    case FusedCore::MatMul:
    case FusedCore::QMatMul:
        columns = std::max<uint64_t>(shape.dimensions()[1], 1);
        chunk = std::max<uint64_t>(FUSED_CHUNK / columns, 1) * columns;
        columns = shape.dimensions()[1];
        inner = input(0).shape().dimensions()[1];
        core_dtype = core == FusedCore::MatMul ? Dtype::int32 : out_dtype;
        break;
    case FusedCore::MatMulEager:
    case FusedCore::QMatMulEager:
        rows = shape.dimensions()[0];
        columns = shape.dimensions()[1];
        inner = input(0).shape().dimensions()[1];
        core_dtype = core == FusedCore::MatMulEager ? Dtype::int32 : out_dtype;
        break;
    case FusedCore::ArgMax:
        inner = input(0).shape().size();
        core_dtype = input(0).dtype();
        break;
    case FusedCore::ReduceSum:
    case FusedCore::ReduceMax: {
        Shape const &in = input(0).shape();
        rows = in.dimensions()[axis];
        inner = dimensions_product(in, axis + 1u, in.rank());
        core_dtype = input(0).dtype();
        break;
    }
    case FusedCore::Concat: {
        // `rows` blocks of a's `inner` bytes, then b's `columns`
        Shape const &a = input(0).shape();
        core_dtype = input(0).dtype();
        uint64_t const slice =
            dimensions_product(a, axis + 1u, a.rank(), dtype_size(core_dtype));
        rows = dimensions_product(a, 0, axis);
        inner = a.dimensions()[axis] * slice;
        columns = input(1).shape().dimensions()[axis] * slice;
        break;
    }
    case FusedCore::CumSumEager:
    case FusedCore::ArgMaxEager:
    case FusedCore::ReduceSumEager:
    case FusedCore::ReduceMaxEager:
    case FusedCore::Gather:
        core_dtype = input(0).dtype();
        // The core's shape is the op's
        core_type = TensorType::checked(core_dtype, shape).value();
        break;
    case FusedCore::Literal:
    case FusedCore::TensorRef:
        core_dtype = core_type.dtype();
        break;
    default:
        break;
    }
    uint8_t *const region = memory + tensors_size_;
    uint8_t *const result = memory + node_offsets_[node];
    size_t const result_size = dtype_size(type.dtype());
    auto const node_data = [&](size_t const i) {
        return memory + node_offsets_[ids[i]];
    };
    // An op whose one instruction pushes the core's result has its core's
    // step write the op's result itself
    bool const core_is_result =
        core != FusedCore::Map && n_instructions == 1 &&
        static_cast<FusedInstruction>(*program) == FusedInstruction::Core;

    for (uint64_t start = 0; start < size; start += chunk) {
        uint64_t const length = std::min(chunk, size - start);
        Slots slots{region + slots_offset, chunk * sizeof(uint64_t)};

        Value core_value{};
        if (is_whole_core(core)) {
            // The whole core, computed at the first chunk, and read a chunk
            // at a time as a tensor is
            uint8_t *const whole =
                core_is_result ? result : memory + product_offsets_[node];
            if (start == 0) {
                switch (core) {
                case FusedCore::MatMulEager:
                    matmul_eager(
                        reinterpret_cast<int8_t *>(node_data(0)),
                        reinterpret_cast<int8_t *>(node_data(1)),
                        reinterpret_cast<int32_t *>(whole),
                        rows,
                        inner,
                        columns);
                    break;
                case FusedCore::QMatMulEager:
                    fuse_kernels::qmatmul(
                        input(0).dtype(),
                        core_dtype,
                        bits,
                        node_data(0),
                        node_data(1),
                        whole,
                        rows,
                        inner,
                        columns);
                    break;
                case FusedCore::Literal:
                    std::memcpy(whole, literal, core_type.size_bytes());
                    break;
                case FusedCore::TensorRef: {
                    if (state == nullptr) {
                        return GraphEvalError::InvalidTensorRef;
                    }
                    Tensor out{core_type, whole};
                    if (load_code_tensor(
                            *state, ref, ByteOrder::LittleEndian, out)
                            .has_error()) {
                        return GraphEvalError::InvalidTensorRef;
                    }
                    break;
                }
                case FusedCore::Concat:
                    fuse_kernels::concat(
                        node_data(0),
                        node_data(1),
                        whole,
                        rows,
                        inner,
                        columns);
                    break;
                case FusedCore::Gather: {
                    Tensor const data{input(0), node_data(0)};
                    Tensor const indices{input(1), node_data(1)};
                    Tensor out{core_type, whole};
                    GraphEvalError const error =
                        fuse_kernels::evaluate_gather(axis, data, indices, out);
                    if (error != GraphEvalError::Success) {
                        return error;
                    }
                    break;
                }
                case FusedCore::CumSumEager:
                case FusedCore::ArgMaxEager:
                case FusedCore::ReduceSumEager:
                case FusedCore::ReduceMaxEager: {
                    Tensor const x{input(0), node_data(0)};
                    Tensor out{core_type, whole};
                    GraphEvalError const error =
                        fuse_kernels::evaluate_eager(core, axis, x, out);
                    if (error != GraphEvalError::Success) {
                        return error;
                    }
                    break;
                }
                default:
                    MONAD_ABORT();
                }
            }
            core_value = Value{
                core_dtype, whole + start * dtype_size(core_dtype), true, -1};
        }
        else if (core != FusedCore::Map) {
            uint32_t const slot = slots.next();
            uint8_t *const out = core_is_result
                                     ? result + start * result_size
                                     : slots.base + slot * slots.bytes;
            uint8_t *const x = node_data(0);
            switch (core) {
            case FusedCore::CumSum:
                visit_dtype(core_dtype, [&]<typename T>() {
                    cumsum_chunk(
                        reinterpret_cast<T const *>(x) + start,
                        reinterpret_cast<T *>(region),
                        reinterpret_cast<T *>(out),
                        start,
                        length,
                        inner,
                        rows);
                });
                break;
            case FusedCore::MatMul:
                matmul_chunk(
                    reinterpret_cast<int8_t *>(x),
                    reinterpret_cast<int8_t *>(node_data(1)),
                    reinterpret_cast<int32_t *>(out),
                    start,
                    length,
                    inner,
                    columns);
                break;
            case FusedCore::QMatMul:
                fuse_kernels::qmatmul(
                    input(0).dtype(),
                    core_dtype,
                    bits,
                    x + start / columns * inner * dtype_size(input(0).dtype()),
                    node_data(1),
                    out,
                    length / columns,
                    inner,
                    columns);
                break;
            case FusedCore::ReduceSum:
            case FusedCore::ReduceMax:
                visit_dtype(core_dtype, [&]<typename T>() {
                    auto const *const xs = reinterpret_cast<T const *>(x);
                    auto *const outs = reinterpret_cast<T *>(out);
                    if (core == FusedCore::ReduceSum) {
                        fuse_kernels::reduce_chunk<T, WrappingAdd>(
                            xs, outs, start, length, rows, inner);
                    }
                    else {
                        fuse_kernels::reduce_chunk<T, Maximum>(
                            xs, outs, start, length, rows, inner);
                    }
                });
                break;
            case FusedCore::ArgMax:
                visit_dtype(core_dtype, [&]<typename T>() {
                    argmax_chunk(
                        reinterpret_cast<T const *>(x),
                        reinterpret_cast<T *>(out),
                        inner);
                });
                break;
            default:
                MONAD_ABORT();
            }
            core_value = Value{core_dtype, out, true, -1};
        }
        if (core_is_result) {
            continue;
        }

        std::array<Value, MAX_FUSED_INSTRUCTIONS> stack;
        size_t top = 0;
        bool result_written = false;
        uint8_t const *q = program;
        for (size_t i = 0; i < n_instructions; i++) {
            bool const last = i + 1 == n_instructions;
            auto const opcode = static_cast<FusedInstruction>(*q++);
            // A computed value's chunk buffer, taken before the inputs' are
            // freed, or the op's result for the last instruction
            auto const destination = [&](Dtype const dtype) {
                uint32_t const slot = slots.next();
                if (last) {
                    result_written = true;
                    return Value{dtype, result + start * result_size, true, -1};
                }
                return Value{
                    dtype,
                    slots.base + slot * slots.bytes,
                    true,
                    static_cast<int32_t>(slot)};
            };
            switch (opcode) {
            case FusedInstruction::Core:
                stack[top++] = core_value;
                break;
            case FusedInstruction::Input: {
                size_t const id = load<uint16_t>(q);
                q += 2;
                TensorType const &input_type = node_types_[id];
                uint64_t const n = input_type.shape().size();
                uint8_t *const data = memory + node_offsets_[id];
                if (n == size || n == 1) {
                    stack[top++] = Value{
                        input_type.dtype(),
                        n == size
                            ? data + start * dtype_size(input_type.dtype())
                            : data,
                        n == size,
                        -1};
                    break;
                }
                Value const value = destination(input_type.dtype());
                visit_dtype(input_type.dtype(), [&]<typename T>() {
                    broadcast_chunk(
                        loops[i].loops,
                        reinterpret_cast<T const *>(data),
                        reinterpret_cast<T *>(value.data),
                        start,
                        length);
                });
                stack[top++] = value;
                break;
            }
            case FusedInstruction::Gather: {
                size_t const data_id = load<uint16_t>(q);
                size_t const index_id = load<uint16_t>(q + 2);
                uint8_t const gather_axis = q[4];
                q += 5;
                TensorType const &data = node_types_[data_id];
                Shape const &data_shape = data.shape();
                Value const value = destination(data.dtype());
                auto const index = fuse_kernels::gather_index(
                    memory + node_offsets_[index_id],
                    node_types_[index_id].dtype(),
                    data_shape.dimensions()[gather_axis]);
                if (!index) {
                    return GraphEvalError::IndexError;
                }
                uint64_t const slice = dimensions_product(
                    data_shape, gather_axis + 1u, data_shape.rank());
                visit_dtype(data.dtype(), [&]<typename T>() {
                    broadcast_chunk(
                        loops[i].loops,
                        reinterpret_cast<T const *>(
                            memory + node_offsets_[data_id]) +
                            *index * slice,
                        reinterpret_cast<T *>(value.data),
                        start,
                        length);
                });
                stack[top++] = value;
                break;
            }
            case FusedInstruction::Constant: {
                auto const dtype = static_cast<Dtype>(*q++);
                q += dtype_size(dtype);
                stack[top++] = Value{
                    dtype,
                    reinterpret_cast<uint8_t *>(&constants[i]),
                    false,
                    -1};
                break;
            }
            case FusedInstruction::Sub:
            case FusedInstruction::Greater:
            case FusedInstruction::Ge:
            case FusedInstruction::Equal:
            case FusedInstruction::Add:
            case FusedInstruction::Mul:
            case FusedInstruction::Max:
            case FusedInstruction::Min: {
                Value const y = stack[--top];
                Value const x = stack[--top];
                Value const value = destination(binary_dtype(opcode, x.dtype));
                slots.release(x);
                slots.release(y);
                run_binary(opcode, x, y, value.data, length);
                stack[top++] = value;
                break;
            }
            case FusedInstruction::QMul:
            case FusedInstruction::QDiv: {
                unsigned const fractional_bits = *q++;
                Value const y = stack[--top];
                Value const x = stack[--top];
                Value const value = destination(x.dtype);
                slots.release(x);
                slots.release(y);
                GraphEvalError const error =
                    visit_dtype(x.dtype, [&]<typename T>() -> GraphEvalError {
                        auto const *const xs =
                            reinterpret_cast<T const *>(x.data);
                        auto const *const ys =
                            reinterpret_cast<T const *>(y.data);
                        auto *const outs = reinterpret_cast<T *>(value.data);
                        if (opcode == FusedInstruction::QMul) {
                            run_op2(
                                xs,
                                ys,
                                outs,
                                length,
                                x.stride,
                                y.stride,
                                FixedPointMul{fractional_bits});
                            return GraphEvalError::Success;
                        }
                        GraphEvalError const check =
                            fuse_kernels::check_denominators(
                                ys, y.stride ? length : 1);
                        if (check != GraphEvalError::Success) {
                            return check;
                        }
                        run_op2(
                            xs,
                            ys,
                            outs,
                            length,
                            x.stride,
                            y.stride,
                            FixedPointDiv{fractional_bits});
                        return GraphEvalError::Success;
                    });
                if (error != GraphEvalError::Success) {
                    return error;
                }
                stack[top++] = value;
                break;
            }
            case FusedInstruction::QExp:
            case FusedInstruction::QInvSqrt: {
                unsigned const fractional_bits = *q++;
                Value const x = stack[--top];
                Value const value = destination(x.dtype);
                slots.release(x);
                GraphEvalError const error =
                    visit_dtype(x.dtype, [&]<typename T>() -> GraphEvalError {
                        auto const *const xs =
                            reinterpret_cast<T const *>(x.data);
                        auto *const outs = reinterpret_cast<T *>(value.data);
                        if (opcode == FusedInstruction::QExp) {
                            run_op1(
                                xs,
                                outs,
                                length,
                                x.stride,
                                FixedPointExp{fractional_bits});
                            return GraphEvalError::Success;
                        }
                        GraphEvalError const check =
                            fuse_kernels::check_inv_sqrt(
                                xs, x.stride ? length : 1);
                        if (check != GraphEvalError::Success) {
                            return check;
                        }
                        run_op1(
                            xs,
                            outs,
                            length,
                            x.stride,
                            FixedPointInvSqrt{fractional_bits});
                        return GraphEvalError::Success;
                    });
                if (error != GraphEvalError::Success) {
                    return error;
                }
                stack[top++] = value;
                break;
            }
            case FusedInstruction::ISqrt: {
                Value const x = stack[--top];
                Value const value = destination(x.dtype);
                slots.release(x);
                visit_dtype(x.dtype, [&]<typename T>() {
                    if constexpr (std::is_unsigned_v<T>) {
                        run_op1(
                            reinterpret_cast<T const *>(x.data),
                            reinterpret_cast<T *>(value.data),
                            length,
                            x.stride,
                            [](T const element) {
                                return floor_sqrt(element);
                            });
                    }
                    else {
                        // Validation rejects signed dtypes
                        MONAD_ABORT();
                    }
                });
                stack[top++] = value;
                break;
            }
            case FusedInstruction::Div: {
                auto const denominator = load<int64_t>(q);
                q += sizeof(int64_t);
                Value const x = stack[--top];
                Value const value = destination(x.dtype);
                slots.release(x);
                bool const power_of_two =
                    denominator > 0 &&
                    std::has_single_bit(static_cast<uint64_t>(denominator));
                visit_dtype(x.dtype, [&]<typename T>() {
                    auto const *const xs = reinterpret_cast<T const *>(x.data);
                    auto *const outs = reinterpret_cast<T *>(value.data);
                    if (power_of_two) {
                        div_pow2_chunk(
                            xs,
                            outs,
                            length,
                            x.stride,
                            static_cast<unsigned>(std::countr_zero(
                                static_cast<uint64_t>(denominator))));
                    }
                    else {
                        div_chunk(xs, outs, length, x.stride, denominator);
                    }
                });
                stack[top++] = value;
                break;
            }
            case FusedInstruction::Saturate: {
                auto const to = static_cast<Dtype>(*q++);
                Value const x = stack[--top];
                Value const value = destination(to);
                slots.release(x);
                visit_dtype(x.dtype, [&]<typename From>() {
                    visit_dtype(to, [&]<typename To>() {
                        run_op1<SaturateOp::Impl<To>>(
                            reinterpret_cast<From const *>(x.data),
                            reinterpret_cast<To *>(value.data),
                            length,
                            x.stride);
                    });
                });
                stack[top++] = value;
                break;
            }
            case FusedInstruction::Where: {
                Value const y = stack[--top];
                Value const x = stack[--top];
                Value const condition = stack[--top];
                Value const value = destination(x.dtype);
                slots.release(condition);
                slots.release(x);
                slots.release(y);
                visit_dtype(x.dtype, [&]<typename T>() {
                    run_op3<WhereOp::Impl<T>>(
                        condition.data,
                        reinterpret_cast<T const *>(x.data),
                        reinterpret_cast<T const *>(y.data),
                        reinterpret_cast<T *>(value.data),
                        length,
                        condition.stride,
                        x.stride,
                        y.stride);
                });
                stack[top++] = value;
                break;
            }
            }
        }
        // The result is a tensor or a constant, which is copied
        if (!result_written) {
            Value const &value = stack[0];
            visit_dtype(value.dtype, [&]<typename T>() {
                run_op1<std::identity>(
                    reinterpret_cast<T const *>(value.data),
                    reinterpret_cast<T *>(result + start * result_size),
                    length,
                    value.stride);
            });
        }
    }
    return GraphEvalError::Success;
}

MONAD_GRAPH_EVAL_NAMESPACE_END
