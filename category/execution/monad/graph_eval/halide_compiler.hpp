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
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <Halide.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include <string>
#include <utility>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// A graph compiled by HalideCompiler: a JIT-compiled Halide pipeline, which
// computes the graph's outputs in place, in memory the caller provides, as
// Compiler's IREE functions do
class HalideCompiledGraph
{
    // Undefined if every output is empty, with nothing to compute
    Halide::Callable callable_;
    // The tensors the pipeline reads as constants, Literals and TensorRefs,
    // which must outlive it
    std::vector<Halide::Buffer<>> constants_;
    // The types of the graph's inputs, then of its outputs, and their
    // dimensions as Halide describes buffers: innermost first, dense. The
    // pipeline's arguments are the inputs, a scalar's as its value, and the
    // outputs with elements
    std::vector<TensorType> arguments_;
    std::vector<std::array<halide_dimension_t, MAX_RANK>> dimensions_;
    size_t n_inputs_;

public:
    HalideCompiledGraph(
        Halide::Callable callable, std::vector<Halide::Buffer<>> constants,
        std::vector<TensorType> arguments, size_t n_inputs);

    // Runs the graph on `inputs`, each a dense row-major tensor of its
    // input's type, in host byte order, writing each output to the memory in
    // `outputs`, as the same. The tensors computed in between are allocated
    // in `scratch`. OutOfMemory if they don't fit, and InternalError if the
    // pipeline fails otherwise
    Result<void>
    run(std::span<uint8_t const *const> inputs,
        std::span<uint8_t *const> outputs, std::span<uint8_t> scratch) const;
};

// Compiles a graph to a Halide pipeline and JIT-compiles it in-process, as
// Compiler does with IREE: each node is a Halide Func, of one loop variable
// per dimension, innermost first, so that a tensor's last dimension is its
// Func's first. The pipeline is scheduled by hand, or by one of Halide's
// autoschedulers
class HalideCompiler
{
    // The graph as a Halide pipeline before it's scheduled, which both
    // compile()s start from
    struct HalidePipeline
    {
        // An ImageParam per input, but a Param for a scalar
        std::vector<Halide::Argument> inputs;
        std::vector<Halide::Func> values; // A Func per node
        std::vector<size_t> readers; // The number of ops reading each node
        // A Func per output with elements, reading its node's, so that a node
        // can be more than one output
        std::vector<Halide::Func> outputs;
        // The types of the inputs, then of all the outputs
        std::vector<TensorType> arguments;
    };

    Graphcode const &gc_;
    std::span<uint8_t const> code_;
    State &state_; // For the code that TensorRefs read

    // The loop variables of every Func, innermost first
    std::array<Halide::Var, MAX_RANK> vars_;
    // The tensors the pipeline reads as constants, for HalideCompiledGraph
    std::vector<Halide::Buffer<>> constants_;
    // The nodes that are scans, and their axes, as Func dimensions, for the
    // hand-written schedule
    std::vector<std::pair<size_t, size_t>> scans_;

    // The Funcs summing matrix products, MatMul's and QMatMul's, with their
    // rows and columns, for the hand-written schedule
    struct Product
    {
        Halide::Func sums;
        int rows;
        int columns;
    };

    std::vector<Product> products_;
    // Whether the graph's inputs and constant tensors are read through
    // Halide's repeat_edge, which clamps every index into bounds. An
    // autoscheduler may compute a Func past its extents, discarding the extra
    // elements, but their reads must still be in bounds
    bool clamp_reads_ = false;

    Result<HalidePipeline> halide_pipeline();
    void halide_schedule(HalidePipeline &);
    HalideCompiledGraph
    halide_compile(HalidePipeline &, Halide::Pipeline &, std::string *ir);

    Halide::Type halide_type(Dtype);
    std::vector<Halide::Var> halide_vars(size_t rank);
    void halide_constrain(Halide::OutputImageParam, Shape const &);
    void halide_vectorize(Halide::Func &, TensorType const &);
    Halide::Expr halide_element(
        Halide::Func const &, Shape const &input, Shape const &output,
        std::vector<Halide::Var> const &);
    Halide::Func halide_constant(TensorType const &, std::span<uint8_t const>);
    Halide::Func halide_reduce(
        size_t axis, size_t input_id, std::vector<Halide::Func> const &values,
        bool sum);
    template <typename Body>
    Halide::Func halide_elementwise(
        std::span<size_t const> input_ids,
        std::vector<Halide::Func> const &values, Body const &body);

    Halide::Func
    halide_op(LiteralOp const &, std::vector<Halide::Func> const &);
    Result<Halide::Func>
    halide_op(TensorRefOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(AddOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(SubOp const &, std::vector<Halide::Func> const &);
    Halide::Func
    halide_op(GreaterOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(GeOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(EqualOp const &, std::vector<Halide::Func> const &);
    Halide::Func
    halide_op(ReshapeOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(WhereOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(CumSumOp const &, std::vector<Halide::Func> const &);
    Halide::Func
    halide_op(SaturateOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(MatMulOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(ArgMaxOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(ArgMinOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(ClipOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(MaxOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(MinOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(MulOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(DivOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(CastOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(ExpandOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(QMulOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(QDivOp const &, std::vector<Halide::Func> const &);
    Halide::Func
    halide_op(QMatMulOp const &, std::vector<Halide::Func> const &);
    Halide::Func
    halide_op(ReduceSumOp const &, std::vector<Halide::Func> const &);
    Halide::Func
    halide_op(ReduceMaxOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(QExpOp const &, std::vector<Halide::Func> const &);
    Halide::Func
    halide_op(QInvSqrtOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(GatherOp const &, std::vector<Halide::Func> const &);
    Halide::Func halide_op(ConcatOp const &, std::vector<Halide::Func> const &);

public:
    // Compiles the graph with the hand-written schedule. If `ir` isn't null,
    // it gets the pipeline as Halide lowers it, as text: its loop nests,
    // vectorized and with the allocations of the Funcs computed at root, for
    // inspecting the code
    Result<HalideCompiledGraph> compile(std::string *ir = nullptr);
    // Compiles the graph with the schedule of `scheduler`, one of the
    // autoschedulers Halide's build has plugins for: Adams2019, Li2018 or
    // Mullapudi2016, with its options. The schedule is for a single thread
    // unless the options give a parallelism above 1. `ir` is as for compile()
    Result<HalideCompiledGraph> compile(
        Halide::AutoschedulerParams const &scheduler,
        std::string *ir = nullptr);
    HalideCompiler(Graphcode const &gc, State &state);
    HalideCompiler(HalideCompiler const &) = delete;
    HalideCompiler(HalideCompiler &&) = delete;
    HalideCompiler &operator=(HalideCompiler const &) = delete;
    HalideCompiler &operator=(HalideCompiler &&) = delete;
};

MONAD_GRAPH_EVAL_NAMESPACE_END
