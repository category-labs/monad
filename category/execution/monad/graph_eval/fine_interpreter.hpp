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

#include <category/core/result.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/fine.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <cstddef>
#include <cstdint>
#include <span>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// A Scalar node's registers, which run() keeps on its stack, so that every
// Scalar node of a run uses the same memory. Defined in fine_interpreter.cpp
struct ScalarRegisters;

// Runs Fine bytecode that validated, on its inputs, allocating nothing and
// checking nothing the validator checked. Each node's data is where the
// validator's node location says: the arena for inputs and most ops, the
// input's data for a Reshape, and the code itself for a Literal, unaligned.
// The outputs are returned in an array and point into the arena or the code.
//
// A Scalar node is computed a chunk of 256 of its output's elements at a
// time. Its registers, in the order the bytecode numbers them, are its
// inputs, its constants, then the registers its fns write. For each chunk,
// every register holds all of the chunk's elements, so kernels take no
// strides:
//
// - an input of the output's shape: the input's own data, not copied;
// - an input of one element, and a constant: its value, copied across the
//   register's block once a node;
// - any other input, which broadcasts: the chunk's elements, copied out of
//   the input into the register's block each chunk;
// - a fn's result. A register is uniform if it holds one value at every
//   position: a constant, an input of one element, or the result of a fn
//   whose operands are all uniform, which runs on one element and is then
//   copied across the chunk. The last fn writes the output's chunk directly.
class FineInterpreter
{
    Finecode const &finecode_;
    State &state_;
    std::span<TensorInput const> const inputs_;
    uint8_t *const arena_;

    // Node `id`'s tensor, in the arena or, for a Literal, in the code. Only
    // the node's own op writes it, so a tensor in the code is never written
    Tensor node(size_t id) const;

    Result<void> check_inputs() const;
    Result<void> load_inputs();

    // Each runs the op whose params start at `code`, the bytecode after its
    // opcode, for node `id`, and moves `code` past it
    Result<void>
    run_scalar(uint8_t const *&code, size_t id, ScalarRegisters &);
    Result<void>
    run_op(FineOp op, uint8_t const *&code, size_t id, ScalarRegisters &);

public:
    FineInterpreter(
        Finecode const &, State &, std::span<TensorInput const> inputs,
        uint8_t *arena);

    Result<GraphOutputs> run();
};

MONAD_GRAPH_EVAL_NAMESPACE_END
