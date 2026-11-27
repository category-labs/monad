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

#include "category/core/assert.h"
#include "category/execution/monad/graph_eval/graph.hpp"
#include "category/execution/monad/graph_eval/graph_eval_error.hpp"
#include <category/core/result.hpp>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>

#include <cstddef>
#include <cstdint>
#include <span>
#include <tuple>
#include <type_traits>
#include <variant>
#include <vector>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

enum class GraphcodeVersion : uint8_t
{
    // As in EIP-3540, the first version is 1
    V1 = 1,
    Invalid
};

using node_id_t = uint16_t;
using register_id_t = uint8_t;

template <>
[[gnu::always_inline]]
inline Result<GraphcodeVersion>
read_next<GraphcodeVersion>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const id,
        read_next<std::underlying_type_t<GraphcodeVersion>>(input));
    if (id >= static_cast<std::underlying_type_t<GraphcodeVersion>>(
                  GraphcodeVersion::Invalid)) {
        return GraphEvalError::GraphValidationError;
    }
    return static_cast<GraphcodeVersion>(id);
}

template <typename P, size_t N>
struct OpInfoImpl
{
    using Params = P;
    static constexpr size_t ARITY = N;
};

template <typename P, size_t N>
struct ScalarFnInfoImpl
{
    using Params = P;
    static constexpr size_t ARITY = N;
};

// The opcodes, as the graph eval MIP numbers them, each given explicitly since
// the bytecode stores them
enum class Opcode : uint8_t
{
    // Elementwise scalar operation.
    // Scalar(Shape outputShape, uint16_t[] inputs)
    Scalar = 0,

    Literal = 1,
    TensorRef = 2,

    Reshape = 3,
    Transpose = 4,
    Concat = 5,

    QMatMul = 6,

    CumSum = 7,

    ArgMin = 8,
    ArgMax = 9,

    ReduceSum = 10,
    ReduceMax = 11,

    Gather = 12,

    Invalid
};

// One more than the largest opcode, so the size of a table indexed by opcode
constexpr size_t N_OPS = static_cast<size_t>(Opcode::Invalid);

template <Opcode>
struct OpInfo;

template <Opcode Op>
using OpParams = OpInfo<Op>::Params;

template <Opcode Op>
constexpr size_t OpArity = OpInfo<Op>::ARITY;

template <>
struct OpInfo<Opcode::Scalar> : OpInfoImpl<Shape, 0>
{
};

template <>
struct OpInfo<Opcode::Literal> : OpInfoImpl<TensorType, 0>
{
};

template <>
struct OpInfo<Opcode::TensorRef>
    : OpInfoImpl<std::tuple<TensorType, Address, uint32_t>, 0>
{
};

template <>
struct OpInfo<Opcode::Reshape> : OpInfoImpl<Shape, 1>
{
};

template <>
struct OpInfo<Opcode::Transpose> : OpInfoImpl<std::tuple<uint8_t, uint8_t>, 1>
{
};

// Params axis and n_inputs. Its n_inputs input ids follow them, read by its
// validator and each engine, as Scalar's are, so its arity here is 0
template <>
struct OpInfo<Opcode::Concat> : OpInfoImpl<std::tuple<uint8_t, uint8_t>, 0>
{
};

template <>
struct OpInfo<Opcode::QMatMul> : OpInfoImpl<std::tuple<uint8_t, Dtype>, 2>
{
};

template <>
struct OpInfo<Opcode::CumSum> : OpInfoImpl<uint8_t, 1>
{
};

template <>
struct OpInfo<Opcode::ArgMin> : OpInfoImpl<uint8_t, 1>
{
};

template <>
struct OpInfo<Opcode::ArgMax> : OpInfoImpl<uint8_t, 1>
{
};

template <>
struct OpInfo<Opcode::ReduceSum> : OpInfoImpl<uint8_t, 1>
{
};

template <>
struct OpInfo<Opcode::ReduceMax> : OpInfoImpl<uint8_t, 1>
{
};

template <>
struct OpInfo<Opcode::Gather> : OpInfoImpl<uint8_t, 2>
{
};

template <>
[[gnu::always_inline]]
inline Result<Opcode> read_next<Opcode>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const id, read_next<std::underlying_type_t<Opcode>>(input));
    // A valid id is one of the enumerators below Invalid, each listed here
    auto const op = static_cast<Opcode>(id);
    switch (op) {
    case Opcode::Scalar:
    case Opcode::Literal:
    case Opcode::TensorRef:
    case Opcode::Reshape:
    case Opcode::Transpose:
    case Opcode::Concat:
    case Opcode::QMatMul:
    case Opcode::CumSum:
    case Opcode::ArgMin:
    case Opcode::ArgMax:
    case Opcode::ReduceSum:
    case Opcode::ReduceMax:
    case Opcode::Gather:
        return op;
    case Opcode::Invalid:
        break;
    }
    return GraphEvalError::InvalidOp;
}

template <>
[[gnu::always_inline]] inline Opcode take<Opcode>(uint8_t const *&code)
{
    return static_cast<Opcode>(take<std::underlying_type_t<Opcode>>(code));
}

template <typename F>
[[gnu::always_inline]]
inline auto visit_op(Opcode const op, F &&f)
{
    switch (op) {
    case Opcode::Scalar:
        return f.template operator()<Opcode::Scalar>();
    case Opcode::Literal:
        return f.template operator()<Opcode::Literal>();
    case Opcode::TensorRef:
        return f.template operator()<Opcode::TensorRef>();
    case Opcode::Reshape:
        return f.template operator()<Opcode::Reshape>();
    case Opcode::Transpose:
        return f.template operator()<Opcode::Transpose>();
    case Opcode::Concat:
        return f.template operator()<Opcode::Concat>();
    case Opcode::QMatMul:
        return f.template operator()<Opcode::QMatMul>();
    case Opcode::CumSum:
        return f.template operator()<Opcode::CumSum>();
    case Opcode::ArgMin:
        return f.template operator()<Opcode::ArgMin>();
    case Opcode::ArgMax:
        return f.template operator()<Opcode::ArgMax>();
    case Opcode::ReduceSum:
        return f.template operator()<Opcode::ReduceSum>();
    case Opcode::ReduceMax:
        return f.template operator()<Opcode::ReduceMax>();
    case Opcode::Gather:
        return f.template operator()<Opcode::Gather>();
    case Opcode::Invalid:
        MONAD_ABORT();
    }
    MONAD_ABORT();
}

enum class ScalarFn : uint8_t
{
    Add,
    Sub,
    Mul,
    Divc, /* uint64_t divisor */
    Div,

    Lt,
    Le,
    Eq,

    Where,

    Min,
    Max,
    Saturate, /* Dtype dtype */

    QMul, /* uint8_t frac_bits */
    QDiv, /* uint8_t frac_bits */
    QExp, /* uint8_t frac_bits */
    QInvSqrt, /* uint8_t frac_bits */

    ISqrt,

    Invalid
};

template <ScalarFn>
struct ScalarFnInfo;

template <ScalarFn Fn>
using FnParams = ScalarFnInfo<Fn>::Params;

template <ScalarFn Fn>
constexpr size_t FnArity = ScalarFnInfo<Fn>::ARITY;

template <>
struct ScalarFnInfo<ScalarFn::Add> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Sub> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Mul> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Divc> : ScalarFnInfoImpl<uint64_t, 1>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Div> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Lt> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Le> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Eq> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Where> : ScalarFnInfoImpl<std::monostate, 3>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Min> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Max> : ScalarFnInfoImpl<std::monostate, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::Saturate> : ScalarFnInfoImpl<Dtype, 1>
{
};

template <>
struct ScalarFnInfo<ScalarFn::QMul> : ScalarFnInfoImpl<uint8_t, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::QDiv> : ScalarFnInfoImpl<uint8_t, 2>
{
};

template <>
struct ScalarFnInfo<ScalarFn::QExp> : ScalarFnInfoImpl<uint8_t, 1>
{
};

template <>
struct ScalarFnInfo<ScalarFn::QInvSqrt> : ScalarFnInfoImpl<uint8_t, 1>
{
};

template <>
struct ScalarFnInfo<ScalarFn::ISqrt> : ScalarFnInfoImpl<std::monostate, 1>
{
};

template <>
[[gnu::always_inline]]
inline Result<ScalarFn> read_next<ScalarFn>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const id, read_next<std::underlying_type_t<ScalarFn>>(input));
    if (id >=
        static_cast<std::underlying_type_t<ScalarFn>>(ScalarFn::Invalid)) {
        return GraphEvalError::InvalidOp;
    }
    return static_cast<ScalarFn>(id);
}

template <>
[[gnu::always_inline]] inline ScalarFn take<ScalarFn>(uint8_t const *&code)
{
    return static_cast<ScalarFn>(take<std::underlying_type_t<ScalarFn>>(code));
}

template <typename F>
[[gnu::always_inline]]
inline auto visit_fn(ScalarFn const fn, F &&f)
{
    switch (fn) {
    case ScalarFn::Add:
        return f.template operator()<ScalarFn::Add>();
    case ScalarFn::Sub:
        return f.template operator()<ScalarFn::Sub>();
    case ScalarFn::Mul:
        return f.template operator()<ScalarFn::Mul>();
    case ScalarFn::Divc:
        return f.template operator()<ScalarFn::Divc>();
    case ScalarFn::Div:
        return f.template operator()<ScalarFn::Div>();
    case ScalarFn::Lt:
        return f.template operator()<ScalarFn::Lt>();
    case ScalarFn::Le:
        return f.template operator()<ScalarFn::Le>();
    case ScalarFn::Eq:
        return f.template operator()<ScalarFn::Eq>();
    case ScalarFn::Where:
        return f.template operator()<ScalarFn::Where>();
    case ScalarFn::Min:
        return f.template operator()<ScalarFn::Min>();
    case ScalarFn::Max:
        return f.template operator()<ScalarFn::Max>();
    case ScalarFn::Saturate:
        return f.template operator()<ScalarFn::Saturate>();
    case ScalarFn::QMul:
        return f.template operator()<ScalarFn::QMul>();
    case ScalarFn::QDiv:
        return f.template operator()<ScalarFn::QDiv>();
    case ScalarFn::QExp:
        return f.template operator()<ScalarFn::QExp>();
    case ScalarFn::QInvSqrt:
        return f.template operator()<ScalarFn::QInvSqrt>();
    case ScalarFn::ISqrt:
        return f.template operator()<ScalarFn::ISqrt>();
    case ScalarFn::Invalid:
        MONAD_ABORT();
    }
    MONAD_ABORT();
}

// Where a node's data is: with this bit set, the rest of a node location is an
// offset from the start of the ops (a Literal's data, in place in the code);
// otherwise it's an offset into the arena, a multiple of TENSOR_DATA_ALIGNMENT
constexpr uint32_t CODE_LOCATION = uint32_t{1} << 31;

class Graphcode
{
    friend class GraphcodeValidator;
    friend class Interpreter;
    friend class FastInterpreter;

    Graphcode() = default;

    uint8_t const *ops_{nullptr};
    size_t n_ops_{0};

    std::vector<TensorType> tensor_types_;
    // Each node's location, as CODE_LOCATION describes: inputs and most
    // ops get arena memory of their own, bump-allocated, each rounded up to
    // TENSOR_DATA_ALIGNMENT; a Reshape shares its input's, and a Literal's is
    // its data in the code, as an offset from ops_
    std::vector<uint32_t> node_locations_;
    size_t n_inputs_{0};
    std::vector<node_id_t> output_ids_;

    GraphEvalError validation_result_{GraphEvalError::InternalError};

public:
    constexpr GraphEvalError validation_result() const
    {
        return validation_result_;
    }

    // Where node `node_id`'s data is, as CODE_LOCATION describes
    constexpr uint32_t node_location(size_t const node_id) const
    {
        return node_locations_[node_id];
    }

    constexpr uint8_t const *ops() const
    {
        return ops_;
    }

    constexpr size_t n_ops() const
    {
        return n_ops_;
    }

    constexpr size_t n_inputs() const
    {
        return n_inputs_;
    }

    constexpr std::vector<node_id_t> const &output_ids() const
    {
        return output_ids_;
    }

    constexpr size_t n_nodes() const
    {
        return n_ops_ + n_inputs_;
    }

    constexpr TensorType const &node_type(size_t node_id) const
    {
        return tensor_types_[node_id];
    }

};

Graphcode validate(std::span<uint8_t const>);

MONAD_GRAPH_EVAL_NAMESPACE_END
