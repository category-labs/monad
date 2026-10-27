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

#include "category/core/assert.h"
#include "category/core/math.hpp"
#include "category/execution/monad/graph_eval/broadcasting.hpp"
#include "category/execution/monad/graph_eval/config.hpp"
#include "category/execution/monad/graph_eval/constants.hpp"
#include "category/execution/monad/graph_eval/interpreter.hpp"
#include "category/execution/monad/graph_eval/matmul.hpp"
#include "category/execution/monad/graph_eval/ops.hpp"
#include <category/execution/monad/graph_eval/lite_compiler.hpp>

#include <algorithm>
#include <bit>
#include <cstdint>
#include <set>
#include <type_traits>
#include <variant>

#include <x86intrin.h>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

// The time of a tensor read until the evaluation's end
constexpr uint64_t END = std::numeric_limits<uint64_t>::max();

class Allocator
{
    std::map<uint32_t, uint32_t> by_offset_; // Offset to size
    std::set<std::pair<uint32_t, uint32_t>> by_size_; // (size, offset)
    uint32_t top_ = 0;
    uint32_t peak_ = 0;

    void insert(uint32_t const offset, uint32_t const size)
    {
        by_offset_.emplace(offset, size);
        by_size_.emplace(size, offset);
    }

    void erase(std::map<uint32_t, uint32_t>::iterator const block)
    {
        by_size_.erase({block->second, block->first});
        by_offset_.erase(block);
    }

public:
    // The most memory placed at once
    uint64_t peak() const
    {
        return peak_;
    }

    // Where to put `size` bytes: the smallest free block they fit in, the
    // lowest of those, or else the top, taking in any free block just below it
    uint32_t allocate(uint32_t const size)
    {
        auto const fit = by_size_.lower_bound({size, 0});
        if (fit != by_size_.end()) {
            auto const [block_size, offset] = *fit;
            erase(by_offset_.find(offset));
            if (block_size > size) {
                insert(offset + size, block_size - size);
            }
            return offset;
        }
        uint32_t offset = top_;
        if (!by_offset_.empty()) {
            auto const below = std::prev(by_offset_.end());
            if (below->first + below->second == top_) {
                offset = below->first;
                erase(below);
            }
        }
        top_ = offset + size;
        peak_ = std::max(peak_, top_);
        return offset;
    }

    // Frees a block, merging it with free neighbors, or lowering the top if
    // it reaches it
    void release(uint32_t offset, uint32_t size)
    {
        auto const next = by_offset_.lower_bound(offset);
        if (next != by_offset_.begin()) {
            auto const previous = std::prev(next);
            if (previous->first + previous->second == offset) {
                offset = previous->first;
                size += previous->second;
                erase(previous);
            }
        }
        if (next != by_offset_.end() && offset + size == next->first) {
            size += next->second;
            erase(next);
        }
        if (offset + size == top_) {
            top_ = offset;
        }
        else {
            insert(offset, size);
        }
    }
};

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_END

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

Result<void> LiteCompiledGraph::run(std::span<uint8_t> scratch)
{
    uint64_t const entry = node_times_ ? __rdtsc() : 0;
    kernel_memory_arenas arenas{scratch.data(), data_blob_.data(), nullptr};
    std::span<uint8_t> kernels{kernel_blob_};
    uint64_t start = node_times_
                         ? node_times_->start_ops(
                               entry, input_offsets_.size(), op_labels_.size())
                         : 0;
    // Ops without kernels, such as literals and reshapes, are recorded when
    // the kernels around them run, as taking no time
    size_t next_op = 0;
    auto const record_ops_until = [&](size_t const end) {
        for (; next_op < end; next_op++) {
            auto const &[op, type] = op_labels_[next_op];
            start = node_times_->end_op(next_op, op, type, start);
        }
    };
    for (size_t k = 0; !kernels.empty(); k++) {
        if (node_times_) {
            record_ops_until(kernel_ops_[k]);
        }
        // TODO: create a type alias for this
        Result<size_t> (*eval_kernel)(uint8_t const *, kernel_memory_arenas &);
        std::memcpy(
            static_cast<void *>(&eval_kernel),
            kernels.data(),
            sizeof(eval_kernel));
        kernels = kernels.subspan(sizeof(eval_kernel));
        BOOST_OUTCOME_TRY(
            auto const offset, eval_kernel(kernels.data(), arenas));
        kernels = kernels.subspan(offset);
        if (node_times_) {
            record_ops_until(kernel_ops_[k] + 1);
        }
    }
    if (node_times_) {
        record_ops_until(op_labels_.size());
        node_times_->end_run(entry, start);
    }
    return outcome::success();
}

// When a tensor's memory is live. Times count ops: the inputs are loaded at
// time 0, and op i runs at time i + 1.
struct Lifetime
{
    // The id of the tensor whose memory this one uses: its own, or, for a
    // Reshape's result, its input's
    size_t buffer;
    uint64_t first; // When it's computed
    uint64_t last; // When its memory is last read, if it's its own
};

LiteCompiler::LiteCompiler(Graphcode const &gc, State &state)
    : gc_(gc)
    , code_(gc.code_span())
    , state_(state) {};

Result<LiteCompiledGraph>
LiteCompiler::compile(Graphcode const &gc, State &state)
{
    LiteCompiler compiler{gc, state};
    BOOST_OUTCOME_TRY(compiler.read_graphcode());
    BOOST_OUTCOME_TRY(compiler.allocate_nodes());
    return compiler.lower();
}

Result<void> LiteCompiler::read_graphcode()
{
    // Repeated from graphcode.cpp, will probably move here
    BOOST_OUTCOME_TRY(auto const magic, read_next<uint16_t>(code_));
    if (MONAD_UNLIKELY(magic != GRAPH_MAGIC)) {
        return GraphEvalError::GraphValidationError;
    }

    BOOST_OUTCOME_TRY(n_inputs_, read_next<uint8_t>(code_));
    if (n_inputs_ > MAX_GRAPH_INPUTS) {
        return GraphEvalError::GraphValidationError;
    }

    for (size_t id = 0; id < n_inputs_; id++) {
        BOOST_OUTCOME_TRY(auto const type, read_next<TensorType>(code_));
        node_types_.push_back(type);
        lifetimes_.push_back(Lifetime{id, 0, 0});
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
    auto const n_nodes = n_inputs_ + n_ops;
    users_.resize(n_inputs_ + n_ops);

    for (uint64_t i = 0; i < n_ops; i++) {
        uint64_t const time = i + 1;
        BOOST_OUTCOME_TRY(
            visit_next(code_, [&]<typename OpT>(OpT const &op) -> Result<void> {
                BOOST_OUTCOME_TRY(auto const type, op.check(node_types_));
                for (size_t const input : op.input_ids) {
                    Lifetime &buffer = lifetimes_[lifetimes_[input].buffer];
                    buffer.last = std::max(buffer.last, time);
                    users_[input] += 1;
                }
                auto const id = ops_.size() + n_inputs_;
                auto const buffer = std::same_as<OpT, ReshapeOp>
                                        ? lifetimes_[op.input_ids[0]].buffer
                                        : id;
                ops_.push_back(op);
                node_types_.push_back(type);
                lifetimes_.push_back(Lifetime{buffer, time, time});
                return outcome::success();
            }));
    }

    // The outputs are read after the last op, when they're encoded
    for (size_t i = 0; i < n_outputs; i++) {
        if (outputs_[i] >= n_nodes) {
            return GraphEvalError::GraphValidationError;
        }
        lifetimes_[lifetimes_[outputs_[i]].buffer].last = END;
        users_[outputs_[i]] += 1;
    }
    return outcome::success();
}

inline Result<void> LiteCompiler::allocate_nodes()
{
    size_t const n_ops = ops_.size();
    size_t const n_nodes = n_ops + n_inputs_;
    node_placements_.resize(n_nodes);
    // The tensors whose memory is freed after each time
    std::vector<std::vector<size_t>> freed_after(n_ops + 1);
    uint32_t next_literal_offset = 0;
    Allocator blocks;
    size_t id = 0;
    for (uint64_t time = 0; time <= n_ops; time++) {
        for (; id < n_nodes && lifetimes_[id].first == time; id++) {
            auto const &lifetime = lifetimes_[id];
            if (lifetime.buffer != id) {
                node_placements_[id] = node_placements_[lifetime.buffer];
                continue;
            }
            auto const size = node_types_[id].size_bytes();
            if (size > ARENA_SIZE) {
                return GraphEvalError::OutOfMemory;
            }
            if (size == 0) {
                // Zero-size tensors don't take up space, but we assign them a
                // valid place nonetheless
                node_placements_[id] = Place{Arena::Memory, 0};
                continue;
            }
            if (id >= n_inputs_ &&
                std::holds_alternative<LiteralOp>(ops_[id - n_inputs_])) {
                // Literal nodes are allocated on the constants arena
                next_literal_offset = round_up<uint32_t>(
                    next_literal_offset, TENSOR_DATA_ALIGNMENT);
                node_placements_[id] =
                    Place{Arena::Literals, next_literal_offset};
                next_literal_offset +=
                    static_cast<uint32_t>(node_types_[id].size_bytes());
            }
            else {
                auto const offset = blocks.allocate(round_up<uint32_t>(
                    static_cast<uint32_t>(size), TENSOR_DATA_ALIGNMENT));
                node_placements_[id] = Place{Arena::Memory, offset};
                if (lifetime.last != END) {
                    freed_after[lifetime.last].push_back(id);
                }
            }
        }
        for (size_t const freed : freed_after[time]) {
            MONAD_DEBUG_ASSERT(node_placements_[freed].arena == Arena::Memory);
            blocks.release(
                node_placements_[freed].offset,
                round_up<uint32_t>(
                    static_cast<uint32_t>(node_types_[freed].size_bytes()),
                    TENSOR_DATA_ALIGNMENT));
        }
    }

    // TODO: charge gas for the arena size
    if (blocks.peak() > ARENA_SIZE) {
        return GraphEvalError::OutOfMemory;
    }

    arena_size_ = blocks.peak();

    return outcome::success();
}

template <typename K>
    requires std::is_trivially_copyable_v<K>
Result<size_t>
eval_kernel(uint8_t const *kernel_ptr, kernel_memory_arenas &arenas)
{
    K k;
    std::memcpy(&k, kernel_ptr, sizeof(K));
    BOOST_OUTCOME_TRY(
        auto const offset, k.eval(kernel_ptr + sizeof(K), arenas));
    return sizeof(K) + offset;
}

template <typename T>
struct CumSumKernel
{
    Place x;
    Place out;
    size_t outer;
    size_t length;
    size_t inner;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        auto const *const xs = x.get_as<T const>(arenas);
        auto *const outs = out.get_as<T>(arenas);

        for (uint64_t block = 0; block < outer; block++) {
            for (uint64_t row = 0; row < length; row++) {
                uint64_t const start = (block * length + row) * inner;
                for (uint64_t i = start; i < start + inner; i++) {
                    outs[i] = row == 0 ? xs[i]
                                       : WrappingAdd{}(outs[i - inner], xs[i]);
                }
            }
        }
        return 0;
    }
};

template <typename T, auto F>
struct ElementwiseKernel2
{
    BroadcastLoops<2> broadcast_loops;
    Place x;
    Place y;
    Place out;

    using Out_T = decltype(F(T(), T()));

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        T const *const xs = x.get_as<T const>(arenas);
        T const *const ys = y.get_as<T const>(arenas);
        Out_T *const outs = out.get_as<Out_T>(arenas);
        for_each_run(
            broadcast_loops,
            [&](auto const &offsets,
                uint64_t start,
                uint64_t length,
                auto const &strides) {
                run_op2<decltype(F)>(
                    xs + offsets[0],
                    ys + offsets[1],
                    outs + start,
                    length,
                    strides[0],
                    strides[1]);
            });
        return 0;
    }
};

template <typename T>
using AddKernel =
    ElementwiseKernel2<T, ([](T const x, T const y) -> T {
                           T result{};
                           (void)__builtin_add_overflow(x, y, &result);
                           return result;
                       })>;

template <typename T>
using SubKernel =
    ElementwiseKernel2<T, ([](T const x, T const y) -> T {
                           T result{};
                           (void)__builtin_sub_overflow(x, y, &result);
                           return result;
                       })>;

template <typename T>
using GreaterKernel =
    ElementwiseKernel2<T, ([](T const x, T const y) -> uint8_t {
                           return uint8_t{std::greater<T>()(x, y)};
                       })>;

template <typename T>
using MulKernel =
    ElementwiseKernel2<T, ([](T const x, T const y) -> widened_t<T> {
                           return WideningMul{}(x, y);
                       })>;

template <typename T>
using MaxKernel = ElementwiseKernel2<T, ([](T const x, T const y) -> T {
                                         return Maximum{}(x, y);
                                     })>;

template <typename T>
using MinKernel = ElementwiseKernel2<T, ([](T const x, T const y) -> T {
                                         return Minimum{}(x, y);
                                     })>;

template <typename T>
struct WhereKernel
{
    BroadcastLoops<3> broadcast_loops;
    Place cond;
    Place x;
    Place y;
    Place out;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        uint8_t const *const conds = cond.get_as<uint8_t const>(arenas);
        T const *const xs = x.get_as<T const>(arenas);
        T const *const ys = y.get_as<T const>(arenas);
        T *const outs = out.get_as<T>(arenas);
        for_each_run(
            broadcast_loops,
            [&](auto const &offsets,
                uint64_t start,
                uint64_t length,
                auto const &strides) {
                run_op3<
                    decltype([](bool const cond, T const left, T const right) -> T {
                        return cond ? left : right;
                    })>(
                    conds + offsets[0],
                    xs + offsets[1],
                    ys + offsets[2],
                    outs + start,
                    length,
                    strides[0],
                    strides[1],
                    strides[2]);
            });
        return 0;
    }
};

template <typename T>
struct DivKernel
{
    Place x;
    Place out;
    size_t size;
    int64_t denominator;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        auto const *const xs = x.get_as<T const>(arenas);
        auto *const outs = out.get_as<T>(arenas);
        for (size_t i = 0; i < size; i++) {
            if constexpr (std::same_as<T, uint64_t>) {
                // x / |denominator| always fits, and negating it wraps
                uint64_t const magnitude =
                    denominator < 0
                        ? uint64_t{0} - static_cast<uint64_t>(denominator)
                        : static_cast<uint64_t>(denominator);
                uint64_t const quotient = xs[i] / magnitude;
                outs[i] = denominator < 0 ? uint64_t{0} - quotient : quotient;
            }
            else if (denominator == -1) {
                // INT64_MIN / -1 overflows, so negate with wrapping instead
                outs[i] = static_cast<T>(
                    uint64_t{0} -
                    static_cast<uint64_t>(static_cast<int64_t>(xs[i])));
            }
            else {
                outs[i] =
                    static_cast<T>(static_cast<int64_t>(xs[i]) / denominator);
            }
        }
        return 0;
    }
};

template <typename T>
struct DivPow2Kernel
{
    Place x;
    Place out;
    size_t size;
    unsigned shift;
    T mask;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        auto const *const xs = x.get_as<T const>(arenas);
        auto *const outs = out.get_as<T>(arenas);
        // Every quotient is 0, and shifting by the type's width is undefined
        if (shift >= 8 * sizeof(T)) {
            std::fill_n(outs, size, T{0});
            return 0;
        }
        if constexpr (std::is_signed_v<T>) {
            // Adding 2^shift - 1 to negative values rounds toward zero
            auto const divide = [shift = shift,
                                 mask = mask](T const value) -> T {
                return static_cast<T>(
                    (value < 0 ? value + mask : value) >> shift);
            };
            run_op1<decltype(divide)>(xs, outs, size, true, divide);
        }
        else {
            auto const divide = [shift = shift](T const value) -> T {
                return static_cast<T>(value >> shift);
            };
            run_op1<decltype(divide)>(xs, outs, size, true, divide);
        }
        return 0;
    }
};

template <typename From, typename To>
struct SaturateKernel
{
    Place x;
    Place out;
    size_t size;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        run_op1<SaturateOp::Impl<To>>(
            x.get_as<From const>(arenas), out.get_as<To>(arenas), size, true);
        return 0;
    }
};

struct MatMulKernel
{
    TensorType x_type;
    TensorType y_type;
    TensorType out_type;
    Place x;
    Place y;
    Place out;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        Tensor out_tensor{out_type, out.get_as<uint8_t>(arenas)};
        matmul_i8(
            Tensor{x_type, x.get_as<uint8_t>(arenas)},
            Tensor{y_type, y.get_as<uint8_t>(arenas)},
            out_tensor);
        return 0;
    }
};

struct MatVecKernel
{
    Place x;
    Place y;
    Place out;
    size_t rows;
    size_t depth;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        auto const *const xs = x.get_as<int8_t const>(arenas);
        auto const *const ys = y.get_as<int8_t const>(arenas);
        auto *const outs = out.get_as<int32_t>(arenas);
        for (size_t row = 0; row < rows; row++) {
            // Can't overflow: at most 65535 products of magnitude 2^14
            int32_t sum = 0;
            for (size_t i = 0; i < depth; i++) {
                sum += int32_t{xs[row * depth + i]} * int32_t{ys[i]};
            }
            outs[row] = sum;
        }
        return 0;
    }
};

template <typename T>
struct ArgMaxKernel
{
    Place x;
    Place out;
    size_t size;

    Result<size_t> eval(uint8_t const *, kernel_memory_arenas &arenas)
    {
        auto const *const xs = x.get_as<T const>(arenas);
        size_t largest = 0;
        for (size_t i = 1; i < size; i++) {
            if (xs[largest] < xs[i]) {
                largest = i;
            }
        }
        *out.get_as<T>(arenas) = static_cast<T>(largest);
        return 0;
    }
};

struct Lowering
{
    LiteCompiler const &compiler;
    std::vector<std::vector<uint8_t>> kernels;
    std::vector<std::vector<uint8_t>> data_bytes;
    std::vector<size_t> kernel_ops;
    std::vector<std::pair<Op, TensorType>> op_labels;

    TensorType type_of(size_t id)
    {
        return compiler.node_types_[id];
    }

    Place place_of(size_t id)
    {
        return compiler.node_placements_[id];
    }

    LiteCompiledGraph pack()
    {
        LiteCompiledGraph result;

        size_t kernel_blob_size = 0;
        for (auto const &k : kernels) {
            kernel_blob_size += k.size();
        }
        result.kernel_blob_.reserve(kernel_blob_size);
        for (auto const &k : kernels) {
            result.kernel_blob_.append_range(k);
        }

        size_t data_blob_size = 0;
        for (auto const &d : data_bytes) {
            data_blob_size += round_up(d.size(), TENSOR_DATA_ALIGNMENT);
        }
        result.data_blob_.reserve(data_blob_size);
        for (auto const &d : data_bytes) {
            result.data_blob_.append_range(d);
            result.data_blob_.resize(
                round_up(result.data_blob_.size(), TENSOR_DATA_ALIGNMENT));
        }

        result.input_offsets_.reserve(compiler.n_inputs_);
        for (size_t i = 0; i < compiler.n_inputs_; i++) {
            auto const place = place_of(i);
            result.input_offsets_.push_back(place.offset);
        }

        result.output_offsets_.reserve(compiler.outputs_.size());
        for (auto const i : compiler.outputs_) {
            auto const place = place_of(i);
            // TODO: allow outputs in other areas?
            MONAD_ASSERT(place.arena == Arena::Memory);
            result.output_offsets_.push_back(place.offset);
        }

        result.kernel_ops_ = std::move(kernel_ops);
        result.op_labels_ = std::move(op_labels);

        return result;
    }

    template <typename K>
        requires std::is_trivially_copyable_v<K>
    void add_kernel(K const &kernel)
    {
        std::vector<uint8_t> blob;
        auto const eval_ptr = &eval_kernel<K>;
        blob.resize(sizeof(eval_ptr) + sizeof(kernel));
        std::memcpy(
            blob.data(),
            static_cast<void const *>(&eval_ptr),
            sizeof(eval_ptr));
        std::memcpy(blob.data() + sizeof(eval_ptr), &kernel, sizeof(kernel));
        kernels.emplace_back(std::move(blob));
    }

    Result<void> operator()(size_t, GraphOpBase const &)
    {
        MONAD_ABORT();
    }

    Result<void> operator()(size_t, LiteralOp const &lit)
    {
        // Literals do not become kernels, they just get added to the data blob.
        auto const [_, span] = lit.params;
        std::vector<uint8_t> literal_data;
        literal_data.assign_range(span);
        data_bytes.emplace_back(std::move(literal_data));
        return outcome::success();
    }

    Result<void> operator()(size_t id, SubOp const &sub)
    {
        auto const &[x_id, y_id] = sub.input_ids;
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<2>({type_of(x_id).shape(), type_of(y_id).shape()}));
        return visit_dtype(type_of(id).dtype(), [&]<typename T>() {
            SubKernel<T> k;
            k.broadcast_loops = loops;
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, CumSumOp const &cumsum)
    {
        auto const &[x_id] = cumsum.input_ids;
        auto const &x_type = type_of(x_id);
        auto const axis = cumsum.params;
        uint64_t outer = 1;
        for (size_t i = 0; i < axis; i++) {
            outer *= x_type.shape().dimensions()[i];
        }
        uint64_t const length = x_type.shape().dimensions()[axis];
        uint64_t inner = 1;
        for (size_t i = axis + 1u; i < type_of(x_id).shape().rank(); i++) {
            inner *= x_type.shape().dimensions()[i];
        }
        return visit_dtype(type_of(id).dtype(), [&]<typename T>() {
            CumSumKernel<T> k;
            k.x = place_of(x_id);
            k.out = place_of(id);
            k.outer = outer;
            k.length = length;
            k.inner = inner;
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, GreaterOp const &gt)
    {
        auto const &[x_id, y_id] = gt.input_ids;
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<2>({type_of(x_id).shape(), type_of(y_id).shape()}));
        return visit_dtype(type_of(x_id).dtype(), [&]<typename T>() {
            GreaterKernel<T> k;
            k.broadcast_loops = loops;
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, WhereOp const &where)
    {
        auto const &[cond_id, x_id, y_id] = where.input_ids;
        BOOST_OUTCOME_TRY(
            auto const broadcast_loops,
            broadcast<3>(
                {type_of(cond_id).shape(),
                 type_of(x_id).shape(),
                 type_of(y_id).shape()}));
        return visit_dtype(type_of(id).dtype(), [&]<typename T>() {
            WhereKernel<T> k;
            k.broadcast_loops = broadcast_loops;
            k.cond = place_of(cond_id);
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t, ReshapeOp const &)
    {
        // A reshape's result shares its input's place, so it needs no kernel
        return outcome::success();
    }

    Result<void> operator()(size_t id, AddOp const &add)
    {
        auto const &[x_id, y_id] = add.input_ids;
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<2>({type_of(x_id).shape(), type_of(y_id).shape()}));
        return visit_dtype(type_of(x_id).dtype(), [&]<typename T>() {
            AddKernel<T> k;
            k.broadcast_loops = loops;
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, MulOp const &mul)
    {
        auto const &[x_id, y_id] = mul.input_ids;
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<2>({type_of(x_id).shape(), type_of(y_id).shape()}));
        return visit_dtype(type_of(x_id).dtype(), [&]<typename T>() {
            MulKernel<T> k;
            k.broadcast_loops = loops;
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, MaxOp const &max)
    {
        auto const &[x_id, y_id] = max.input_ids;
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<2>({type_of(x_id).shape(), type_of(y_id).shape()}));
        return visit_dtype(type_of(x_id).dtype(), [&]<typename T>() {
            MaxKernel<T> k;
            k.broadcast_loops = loops;
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, MinOp const &min)
    {
        auto const &[x_id, y_id] = min.input_ids;
        BOOST_OUTCOME_TRY(
            auto const loops,
            broadcast<2>({type_of(x_id).shape(), type_of(y_id).shape()}));
        return visit_dtype(type_of(x_id).dtype(), [&]<typename T>() {
            MinKernel<T> k;
            k.broadcast_loops = loops;
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, DivOp const &div)
    {
        auto const &[x_id] = div.input_ids;
        auto const denominator = static_cast<uint64_t>(div.params);
        return visit_dtype(type_of(id).dtype(), [&]<typename T>() {
            if (div.params > 0 && std::has_single_bit(denominator)) {
                DivPow2Kernel<T> k;
                k.x = place_of(x_id);
                k.out = place_of(id);
                k.size = type_of(id).shape().size();
                k.shift = static_cast<unsigned>(std::countr_zero(denominator));
                k.mask = k.shift < 8 * sizeof(T)
                             ? static_cast<T>((uint64_t{1} << k.shift) - 1)
                             : T{0};
                add_kernel(k);
                return outcome::success();
            }
            DivKernel<T> k;
            k.x = place_of(x_id);
            k.out = place_of(id);
            k.size = type_of(id).shape().size();
            k.denominator = div.params;
            add_kernel(k);
            return outcome::success();
        });
    }

    Result<void> operator()(size_t id, SaturateOp const &saturate)
    {
        auto const &[x_id] = saturate.input_ids;
        return visit_dtype(type_of(x_id).dtype(), [&]<typename From>() {
            return visit_dtype(saturate.params, [&]<typename To>() {
                SaturateKernel<From, To> k;
                k.x = place_of(x_id);
                k.out = place_of(id);
                k.size = type_of(id).shape().size();
                add_kernel(k);
                return outcome::success();
            });
        });
    }

    Result<void> operator()(size_t id, MatMulOp const &matmul_op)
    {
        auto const &[x_id, y_id] = matmul_op.input_ids;
        auto const x_type = type_of(x_id);
        if (type_of(y_id).shape().dimensions()[1] == 1) {
            MatVecKernel k;
            k.x = place_of(x_id);
            k.y = place_of(y_id);
            k.out = place_of(id);
            k.rows = x_type.shape().dimensions()[0];
            k.depth = x_type.shape().dimensions()[1];
            add_kernel(k);
            return outcome::success();
        }
        MatMulKernel k;
        k.x_type = x_type;
        k.y_type = type_of(y_id);
        k.out_type = type_of(id);
        k.x = place_of(x_id);
        k.y = place_of(y_id);
        k.out = place_of(id);
        add_kernel(k);
        return outcome::success();
    }

    Result<void> operator()(size_t id, ArgMaxOp const &argmax)
    {
        auto const &[x_id] = argmax.input_ids;
        return visit_dtype(type_of(x_id).dtype(), [&]<typename T>() {
            ArgMaxKernel<T> k;
            k.x = place_of(x_id);
            k.out = place_of(id);
            k.size = type_of(x_id).shape().size();
            add_kernel(k);
            return outcome::success();
        });
    }
};

Result<LiteCompiledGraph> LiteCompiler::lower()
{
    Lowering lowering{*this};
    for (size_t i = 0; i < ops_.size(); i++) {
        auto const id = i + n_inputs_;
        auto const &node = ops_[i];
        BOOST_OUTCOME_TRY(std::visit(
            ([&]<typename OpT>(OpT op) {
                lowering.op_labels.emplace_back(OpT::OPCODE, node_types_[id]);
                return lowering(id, op);
            }),
            node));
        lowering.kernel_ops.resize(lowering.kernels.size(), i);
    }

    return lowering.pack();
}

MONAD_GRAPH_EVAL_NAMESPACE_END
