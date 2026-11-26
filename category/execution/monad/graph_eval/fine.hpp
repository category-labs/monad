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

enum class FineVersion : uint8_t
{
    // As in EIP-3540, the first version is 1
    V1 = 1,
    Invalid
};

using node_id_t = uint16_t;
using register_id_t = uint8_t;

template<>
[[gnu::always_inline]]
inline Result<FineVersion> read_next<FineVersion>(std::span<uint8_t const> &input) {
    BOOST_OUTCOME_TRY(
        auto const id, read_next<std::underlying_type_t<FineVersion>>(input));
    if (id >= static_cast<std::underlying_type_t<FineVersion>>(FineVersion::Invalid)) {
        return GraphEvalError::GraphValidationError;
    }
    return static_cast<FineVersion>(id);
}

template <typename P, size_t N>
struct FineOpInfoImpl
{
    using Params = P;
    static constexpr size_t ARITY = N;
};

template <typename P, size_t N>
struct FineFnInfoImpl
{
    using Params = P;
    static constexpr size_t ARITY = N;
};

// The opcodes, as the graph eval MIP numbers them, each given explicitly since
// the bytecode stores them
enum class FineOp : uint8_t
{
    // Elementwise scalar operation.
    // Scalar(Shape outputShape, uint16_t[] inputs)
    Scalar = 0,

    Literal = 1,
    TensorRef = 2,

    Reshape = 3,
    // Id 4 is the MIP's Transpose, which isn't implemented, so read_next
    // rejects it as an invalid opcode
    Concat = 5,

    QMatMul = 6,

    CumSum = 7,

    ArgMin = 8,
    ArgMax = 9,

    ReduceSum = 10,
    ReduceMax = 11,

    Gather = 12,

    // Temporary, until it's removed: not in the MIP, where QMatMul with
    // frac_bits 0 replaces it. It has the first id after the MIP's opcodes
    MatMul = 13,

    Invalid
};

// One more than the largest opcode, so the size of a table indexed by opcode.
// Not every id below it is an op: id 4, the MIP's Transpose, has none
constexpr size_t N_FINE_OPS = static_cast<size_t>(FineOp::Invalid);

template <FineOp>
struct FineOpInfo;

template <FineOp Op>
using OpParams = FineOpInfo<Op>::Params;

template <FineOp Op>
constexpr size_t OpArity = FineOpInfo<Op>::ARITY;

template <>
struct FineOpInfo<FineOp::Scalar> : FineOpInfoImpl<Shape, 0>
{
};

template <>
struct FineOpInfo<FineOp::Literal> : FineOpInfoImpl<TensorType, 0>
{
};

template <>
struct FineOpInfo<FineOp::TensorRef>
    : FineOpInfoImpl<std::tuple<TensorType, Address, uint32_t>, 0>
{
};

template <>
struct FineOpInfo<FineOp::Reshape> : FineOpInfoImpl<Shape, 1>
{
};

template <>
struct FineOpInfo<FineOp::Concat> : FineOpInfoImpl<uint8_t, 2>
{
};

template <>
struct FineOpInfo<FineOp::MatMul> : FineOpInfoImpl<std::monostate, 2>
{
};

template <>
struct FineOpInfo<FineOp::QMatMul>
    : FineOpInfoImpl<std::tuple<uint8_t, Dtype>, 2>
{
};

template <>
struct FineOpInfo<FineOp::CumSum> : FineOpInfoImpl<uint8_t, 1>
{
};

template <>
struct FineOpInfo<FineOp::ArgMin> : FineOpInfoImpl<std::monostate, 1>
{
};

template <>
struct FineOpInfo<FineOp::ArgMax> : FineOpInfoImpl<std::monostate, 1>
{
};

template <>
struct FineOpInfo<FineOp::ReduceSum> : FineOpInfoImpl<uint8_t, 1>
{
};

template <>
struct FineOpInfo<FineOp::ReduceMax> : FineOpInfoImpl<uint8_t, 1>
{
};

template <>
struct FineOpInfo<FineOp::Gather> : FineOpInfoImpl<uint8_t, 2>
{
};

template <>
[[gnu::always_inline]]
inline Result<FineOp> read_next<FineOp>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const id, read_next<std::underlying_type_t<FineOp>>(input));
    // A valid id is one of the enumerators below Invalid, not any id below it,
    // since id 4 has no op
    auto const op = static_cast<FineOp>(id);
    switch (op) {
    case FineOp::Scalar:
    case FineOp::Literal:
    case FineOp::TensorRef:
    case FineOp::Reshape:
    case FineOp::Concat:
    case FineOp::QMatMul:
    case FineOp::CumSum:
    case FineOp::ArgMin:
    case FineOp::ArgMax:
    case FineOp::ReduceSum:
    case FineOp::ReduceMax:
    case FineOp::Gather:
    case FineOp::MatMul:
        return op;
    case FineOp::Invalid:
        break;
    }
    return GraphEvalError::InvalidOp;
}

template <>
[[gnu::always_inline]] inline FineOp take<FineOp>(uint8_t const *&code)
{
    return static_cast<FineOp>(take<std::underlying_type_t<FineOp>>(code));
}

template <typename F>
[[gnu::always_inline]]
inline auto visit_op(FineOp const op, F &&f)
{
    switch (op) {
    case FineOp::Scalar:
        return f.template operator()<FineOp::Scalar>();
    case FineOp::Literal:
        return f.template operator()<FineOp::Literal>();
    case FineOp::TensorRef:
        return f.template operator()<FineOp::TensorRef>();
    case FineOp::Reshape:
        return f.template operator()<FineOp::Reshape>();
    case FineOp::Concat:
        return f.template operator()<FineOp::Concat>();
    case FineOp::MatMul:
        return f.template operator()<FineOp::MatMul>();
    case FineOp::QMatMul:
        return f.template operator()<FineOp::QMatMul>();
    case FineOp::CumSum:
        return f.template operator()<FineOp::CumSum>();
    case FineOp::ArgMin:
        return f.template operator()<FineOp::ArgMin>();
    case FineOp::ArgMax:
        return f.template operator()<FineOp::ArgMax>();
    case FineOp::ReduceSum:
        return f.template operator()<FineOp::ReduceSum>();
    case FineOp::ReduceMax:
        return f.template operator()<FineOp::ReduceMax>();
    case FineOp::Gather:
        return f.template operator()<FineOp::Gather>();
    case FineOp::Invalid:
        MONAD_ABORT();
    }
    MONAD_ABORT();
}

enum class FineFn : uint8_t
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

    // An experiment: Add's type and behavior, which the interpreter runs
    // with a kernel of AVX-512 intrinsics inlined into run_scalar
    FAdd,

    Invalid
};

template <FineFn>
struct FineFnInfo;

template <FineFn Fn>
using FnParams = FineFnInfo<Fn>::Params;

template <FineFn Fn>
constexpr size_t FnArity = FineFnInfo<Fn>::ARITY;


template <>
struct FineFnInfo<FineFn::Add> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Sub> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Mul> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Divc> : FineFnInfoImpl<uint64_t, 1>
{
};

template <>
struct FineFnInfo<FineFn::Div> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Lt> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Le> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Eq> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Where> : FineFnInfoImpl<std::monostate, 3>
{
};

template <>
struct FineFnInfo<FineFn::Min> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Max> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
struct FineFnInfo<FineFn::Saturate> : FineFnInfoImpl<Dtype, 1>
{
};

template <>
struct FineFnInfo<FineFn::QMul> : FineFnInfoImpl<uint8_t, 2>
{
};

template <>
struct FineFnInfo<FineFn::QDiv> : FineFnInfoImpl<uint8_t, 2>
{
};

template <>
struct FineFnInfo<FineFn::QExp> : FineFnInfoImpl<uint8_t, 1>
{
};

template <>
struct FineFnInfo<FineFn::QInvSqrt> : FineFnInfoImpl<uint8_t, 1>
{
};

template <>
struct FineFnInfo<FineFn::ISqrt> : FineFnInfoImpl<std::monostate, 1>
{
};

template <>
struct FineFnInfo<FineFn::FAdd> : FineFnInfoImpl<std::monostate, 2>
{
};

template <>
[[gnu::always_inline]]
inline Result<FineFn> read_next<FineFn>(std::span<uint8_t const> &input)
{
    BOOST_OUTCOME_TRY(
        auto const id, read_next<std::underlying_type_t<FineFn>>(input));
    if (id >= static_cast<std::underlying_type_t<FineFn>>(FineFn::Invalid)) {
        return GraphEvalError::InvalidOp;
    }
    return static_cast<FineFn>(id);
}

template <>
[[gnu::always_inline]] inline FineFn take<FineFn>(uint8_t const *&code)
{
    return static_cast<FineFn>(take<std::underlying_type_t<FineFn>>(code));
}

template <typename F>
[[gnu::always_inline]]
inline auto visit_fn(FineFn const fn, F &&f)
{
    switch (fn) {
    case FineFn::Add:
        return f.template operator()<FineFn::Add>();
    case FineFn::Sub:
        return f.template operator()<FineFn::Sub>();
    case FineFn::Mul:
        return f.template operator()<FineFn::Mul>();
    case FineFn::Divc:
        return f.template operator()<FineFn::Divc>();
    case FineFn::Div:
        return f.template operator()<FineFn::Div>();
    case FineFn::Lt:
        return f.template operator()<FineFn::Lt>();
    case FineFn::Le:
        return f.template operator()<FineFn::Le>();
    case FineFn::Eq:
        return f.template operator()<FineFn::Eq>();
    case FineFn::Where:
        return f.template operator()<FineFn::Where>();
    case FineFn::Min:
        return f.template operator()<FineFn::Min>();
    case FineFn::Max:
        return f.template operator()<FineFn::Max>();
    case FineFn::Saturate:
        return f.template operator()<FineFn::Saturate>();
    case FineFn::QMul:
        return f.template operator()<FineFn::QMul>();
    case FineFn::QDiv:
        return f.template operator()<FineFn::QDiv>();
    case FineFn::QExp:
        return f.template operator()<FineFn::QExp>();
    case FineFn::QInvSqrt:
        return f.template operator()<FineFn::QInvSqrt>();
    case FineFn::ISqrt:
        return f.template operator()<FineFn::ISqrt>();
    case FineFn::FAdd:
        return f.template operator()<FineFn::FAdd>();
    case FineFn::Invalid:
        MONAD_ABORT();
    }
    MONAD_ABORT();
}

// Where a node's data is: with this bit set, the rest of a node location is an
// offset from the start of the ops (a Literal's data, in place in the code);
// otherwise it's an offset into the arena, a multiple of TENSOR_DATA_ALIGNMENT
constexpr uint32_t FINE_CODE_LOCATION = uint32_t{1} << 31;

class Finecode
{
    friend class FinecodeValidator;
    friend class FineInterpreter;
    friend class FineFastInterpreter;

    Finecode() = default;

    uint8_t const *ops_{nullptr};
    size_t n_ops_{0};

    std::vector<TensorType> tensor_types_;
    // Each node's location, as FINE_CODE_LOCATION describes: inputs and most
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

    // Where node `node_id`'s data is, as FINE_CODE_LOCATION describes
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

Finecode validate(std::span<uint8_t const>);

MONAD_GRAPH_EVAL_NAMESPACE_END
