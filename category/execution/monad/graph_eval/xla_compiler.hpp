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
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/ops.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/execution/monad/graph_eval/types.hpp>
#include <category/execution/monad/graph_eval/xla/monad_xla/monad_xla.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <set>
#include <span>
#include <string>
#include <string_view>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

// A graph XlaCompiler compiled: an HLO module compiled by XLA's CPU compiler,
// which libmonad_xla.so runs with XLA's NanoRt runtime, on the calling thread
class XlaCompiledGraph
{
    struct Destroy
    {
        void operator()(monad_xla_executable *) const;
    };

    std::unique_ptr<monad_xla_executable, Destroy> executable_;
    size_t n_inputs_;
    size_t n_outputs_;
    // The bytes of the values XLA keeps in between
    size_t temp_size_;

public:
    XlaCompiledGraph(
        monad_xla_executable *executable, size_t n_inputs, size_t n_outputs);

    // Runs the graph on `inputs`, each a dense row-major tensor of its
    // input's type, in host byte order, writing each output to the memory in
    // `outputs`, as the same. The values in between are in `scratch`. Every
    // input, output and scratch must be TENSOR_DATA_ALIGNMENT-aligned, as
    // XLA's kernels assume 64-byte-aligned buffers. OutOfMemory if the values
    // in between don't fit, and InternalError if XLA fails otherwise
    Result<void>
    run(std::span<uint8_t const *const> inputs,
        std::span<uint8_t *const> outputs, std::span<uint8_t> scratch) const;
};

// Compiles a graph with XLA: lowers it to an HLO module, as text, which
// libmonad_xla.so parses and compiles for a Zen 4 CPU and a single thread
class XlaCompiler
{
    Graphcode const &gc_;
    std::span<uint8_t const> code_;
    State &state_; // For the code that TensorRefs read

    // The HLO module being built: the computations its instructions call,
    // such as reductions' adds, by name, and their text; and the entry
    // computation's instructions
    std::set<std::string> computation_names_;
    std::string computations_;
    std::string entry_;
    size_t next_name_ = 0;

    std::string hlo_name();
    std::string
    hlo_append(std::string_view shape, std::string_view instruction);
    std::string hlo_constant(Dtype, __int128 value);
    std::string hlo_splat(Dtype, __int128 value, Shape const &);
    std::string hlo_broadcast(
        std::string const &value, TensorType const &type, Shape const &shape);
    std::string hlo_convert(std::string const &value, Dtype, Shape const &);
    std::string hlo_argmax_computation(Dtype);
    // The node's inputs, broadcast to its shape, and its type
    std::vector<std::string> hlo_operands(
        std::span<size_t const> input_ids,
        std::vector<std::string> const &values);
    template <typename F>
    std::string hlo_elementwise(
        std::span<size_t const> input_ids,
        std::vector<std::string> const &values, F const &body);

    std::string xla_op(LiteralOp const &, std::vector<std::string> const &);
    Result<std::string>
    xla_op(TensorRefOp const &, std::vector<std::string> const &);
    std::string xla_op(AddOp const &, std::vector<std::string> const &);
    std::string xla_op(SubOp const &, std::vector<std::string> const &);
    std::string xla_op(GreaterOp const &, std::vector<std::string> const &);
    std::string xla_op(GeOp const &, std::vector<std::string> const &);
    std::string xla_op(EqualOp const &, std::vector<std::string> const &);
    std::string xla_op(ReshapeOp const &, std::vector<std::string> const &);
    std::string xla_op(WhereOp const &, std::vector<std::string> const &);
    std::string xla_op(CumSumOp const &, std::vector<std::string> const &);
    std::string xla_op(SaturateOp const &, std::vector<std::string> const &);
    std::string xla_op(MatMulOp const &, std::vector<std::string> const &);
    std::string xla_op(ArgMaxOp const &, std::vector<std::string> const &);
    std::string xla_op(ArgMinOp const &, std::vector<std::string> const &);
    std::string xla_op(ClipOp const &, std::vector<std::string> const &);
    std::string xla_op(MaxOp const &, std::vector<std::string> const &);
    std::string xla_op(MinOp const &, std::vector<std::string> const &);
    std::string xla_op(MulOp const &, std::vector<std::string> const &);
    std::string xla_op(DivOp const &, std::vector<std::string> const &);
    std::string xla_op(CastOp const &, std::vector<std::string> const &);
    std::string xla_op(ExpandOp const &, std::vector<std::string> const &);
    std::string xla_op(QMulOp const &, std::vector<std::string> const &);
    std::string xla_op(QDivOp const &, std::vector<std::string> const &);
    std::string xla_op(QMatMulOp const &, std::vector<std::string> const &);
    std::string xla_op(ReduceSumOp const &, std::vector<std::string> const &);
    std::string xla_op(ReduceMaxOp const &, std::vector<std::string> const &);
    std::string xla_op(QExpOp const &, std::vector<std::string> const &);
    std::string xla_op(QInvSqrtOp const &, std::vector<std::string> const &);
    std::string xla_op(GatherOp const &, std::vector<std::string> const &);
    std::string xla_op(ConcatOp const &, std::vector<std::string> const &);

    // The graph as an HLO module, as text
    Result<std::string> hlo_module();

public:
    // Compiles the graph. If `ir` isn't null, it gets the HLO module as text,
    // as emitted and after XLA's HLO passes, for inspecting the code
    Result<XlaCompiledGraph> compile(std::string *ir = nullptr);
    XlaCompiler(Graphcode const &gc, State &state);
    XlaCompiler(XlaCompiler const &) = delete;
    XlaCompiler(XlaCompiler &&) = delete;
    XlaCompiler &operator=(XlaCompiler const &) = delete;
    XlaCompiler &operator=(XlaCompiler &&) = delete;
};

MONAD_GRAPH_EVAL_NAMESPACE_END
