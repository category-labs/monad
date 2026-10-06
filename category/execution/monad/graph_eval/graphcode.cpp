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
#include <category/core/result.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/graph.hpp>
#include <category/execution/monad/graph_eval/graph_eval_error.hpp>
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <limits>
#include <map>
#include <set>
#include <span>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_ANONYMOUS_NAMESPACE_BEGIN

GraphEvalError as_graph_eval_error(Result<void> const &result)
{
    if (!result.has_error()) {
        return GraphEvalError::Success;
    }
    else if (
        result.error().domain() ==
        system_error2::quick_status_code_from_enum_code<
            GraphEvalError>::domain_type::get()) {
        return static_cast<GraphEvalError>(result.error().value());
    }
    else {
        return GraphEvalError::InternalError;
    }
}

// The time of a tensor read until the evaluation's end
constexpr uint64_t END = std::numeric_limits<uint64_t>::max();

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

// The type of the tensor an op computes, as the op's check() works it out,
// with `input_ids` replaced by the node ids of the op's inputs
Result<TensorType> check_op(
    Op const op, std::span<uint8_t const> &graphcode,
    std::vector<TensorType> const &types, std::vector<uint16_t> &input_ids)
{
    switch (op) {
    case Op::Literal:
        return LiteralOp{}.check(graphcode, types, input_ids);
    case Op::Add:
        return AddOp{}.check(graphcode, types, input_ids);
    case Op::Sub:
        return SubOp{}.check(graphcode, types, input_ids);
    case Op::Mul:
        return MulOp{}.check(graphcode, types, input_ids);
    case Op::Max:
        return MaxOp{}.check(graphcode, types, input_ids);
    case Op::Min:
        return MinOp{}.check(graphcode, types, input_ids);
    case Op::Greater:
        return GreaterOp{}.check(graphcode, types, input_ids);
    case Op::Ge:
        return GeOp{}.check(graphcode, types, input_ids);
    case Op::Equal:
        return EqualOp{}.check(graphcode, types, input_ids);
    case Op::Reshape:
        return ReshapeOp{}.check(graphcode, types, input_ids);
    case Op::Where:
        return WhereOp{}.check(graphcode, types, input_ids);
    case Op::Saturate:
        return SaturateOp{}.check(graphcode, types, input_ids);
    case Op::Expand:
        return ExpandOp{}.check(graphcode, types, input_ids);
    case Op::Div:
        return DivOp{}.check(graphcode, types, input_ids);
    case Op::MatMul:
        return MatMulOp{}.check(graphcode, types, input_ids);
    case Op::ArgMax:
        return ArgMaxOp{}.check(graphcode, types, input_ids);
    case Op::CumSum:
        return CumSumOp{}.check(graphcode, types, input_ids);
    case Op::TensorRef:
    case Op::ArgMin:
    case Op::Clip:
    case Op::Cast:
        // Not implemented yet; the interpreter fails on them
        return GraphEvalError::InternalError;
    }
    MONAD_ABORT();
}

// The free memory below the top of the memory placed so far, as blocks keyed by
// offset, to merge neighbors, and by size, to find the best fit
class FreeBlocks
{
    std::map<uint64_t, uint64_t> by_offset_; // Offset to size
    std::set<std::pair<uint64_t, uint64_t>> by_size_; // (size, offset)
    uint64_t top_ = 0;
    uint64_t peak_ = 0;

    void insert(uint64_t const offset, uint64_t const size)
    {
        by_offset_.emplace(offset, size);
        by_size_.emplace(size, offset);
    }

    void erase(std::map<uint64_t, uint64_t>::iterator const block)
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
    uint64_t allocate(uint64_t const size)
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
        uint64_t offset = top_;
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
    void release(uint64_t offset, uint64_t size)
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

Graphcode::Graphcode(std::span<uint8_t const> code)
    : code_(code.data())
    , code_size_(code.size())
{
    validation_result_ = as_graph_eval_error(compute_tensor_allocations());
}

// Works out every tensor's type and when it's live, by reading through the
// graphcode with the ops' check(), then places the tensors in the arena in the
// order they're computed, each in the best-fitting block of memory freed by
// tensors no longer live, or else at the top of the memory placed so far. A
// tensor's memory is freed after the last op that reads it, once that op's own
// tensor is placed, so that an op's output never overlaps its inputs. Each
// placement and release takes O(log n).
Result<void> Graphcode::compute_tensor_allocations()
{
    std::span<uint8_t const> code = code_span();
    std::vector<TensorType> types;
    std::vector<Lifetime> lifetimes;

    // Each tensor's type and lifetime, in id order

    // The magic number, which the interpreter checks
    BOOST_OUTCOME_TRY(read_next<uint16_t>(code));

    BOOST_OUTCOME_TRY(auto const n_inputs, read_next<uint8_t>(code));
    if (n_inputs > MAX_GRAPH_INPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    for (size_t id = 0; id < n_inputs; id++) {
        BOOST_OUTCOME_TRY(auto const dtype, read_next<Dtype>(code));
        BOOST_OUTCOME_TRY(auto const shape, read_next<Shape>(code));
        BOOST_OUTCOME_TRY(tensor_size_bytes(dtype, shape));
        types.push_back(TensorType{dtype, shape});
        lifetimes.push_back(Lifetime{id, 0, 0});
    }

    BOOST_OUTCOME_TRY(auto const n_outputs, read_next<uint8_t>(code));
    if (n_outputs > MAX_GRAPH_OUTPUTS) {
        return GraphEvalError::GraphValidationError;
    }
    std::array<uint16_t, MAX_GRAPH_OUTPUTS> outputs{};
    for (size_t i = 0; i < n_outputs; i++) {
        BOOST_OUTCOME_TRY(outputs[i], read_next<uint16_t>(code));
    }

    BOOST_OUTCOME_TRY(auto const n_ops, read_next<uint16_t>(code));
    std::vector<uint16_t> input_ids;
    for (uint64_t time = 1; time <= n_ops; time++) {
        BOOST_OUTCOME_TRY(auto const opcode, read_next<uint16_t>(code));
        if (opcode > static_cast<uint16_t>(Op::Last_valid_op)) {
            return GraphEvalError::GraphValidationError;
        }
        auto const op = static_cast<Op>(opcode);
        BOOST_OUTCOME_TRY(
            auto const type, check_op(op, code, types, input_ids));
        BOOST_OUTCOME_TRY(tensor_size_bytes(type.dtype, type.shape));

        for (uint16_t const input : input_ids) {
            Lifetime &buffer = lifetimes[lifetimes[input].buffer];
            buffer.last = std::max(buffer.last, time);
        }
        size_t const id = types.size();
        size_t const buffer =
            op == Op::Reshape ? lifetimes[input_ids[0]].buffer : id;
        types.push_back(type);
        lifetimes.push_back(Lifetime{buffer, time, time});
    }

    // The outputs are read after the last op, when they're encoded
    for (size_t i = 0; i < n_outputs; i++) {
        if (outputs[i] >= types.size()) {
            return GraphEvalError::GraphValidationError;
        }
        lifetimes[lifetimes[outputs[i]].buffer].last = END;
    }

    // Each tensor's offset, in the order the tensors are computed. A tensor
    // bigger than the arena could never fit, and keeping sizes within it keeps
    // the offsets from overflowing.
    std::vector<uint64_t> offsets(types.size(), 0);
    // The tensors whose memory is freed after each time
    std::vector<std::vector<size_t>> freed_after(n_ops + 1);
    FreeBlocks blocks;
    size_t id = 0;
    for (uint64_t time = 0; time <= n_ops; time++) {
        for (; id < types.size() && lifetimes[id].first == time; id++) {
            Lifetime const &lifetime = lifetimes[id];
            if (lifetime.buffer != id) {
                offsets[id] = offsets[lifetime.buffer];
                continue;
            }
            uint64_t const size = types[id].size_bytes();
            if (size > ARENA_SIZE) {
                return GraphEvalError::OutOfMemory;
            }
            if (size == 0) {
                continue;
            }
            offsets[id] = blocks.allocate(round_up(size, IREE_ALIGNMENT));
            if (lifetime.last != END) {
                freed_after[lifetime.last].push_back(id);
            }
        }
        for (size_t const freed : freed_after[time]) {
            blocks.release(
                offsets[freed],
                round_up(types[freed].size_bytes(), IREE_ALIGNMENT));
        }
    }
    // TODO: charge gas for the arena size
    if (blocks.peak() > ARENA_SIZE) {
        return GraphEvalError::OutOfMemory;
    }

    arena_size_ = blocks.peak();
    tensor_allocation_records_.reserve(types.size());
    for (size_t i = 0; i < types.size(); i++) {
        tensor_allocation_records_.push_back(
            TensorAllocationRecord{offsets[i], types[i]});
    }
    return outcome::success();
}

MONAD_GRAPH_EVAL_NAMESPACE_END
