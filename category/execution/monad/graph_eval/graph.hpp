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

#include <category/core/assert.h>
#include <category/execution/monad/graph_eval/config.hpp>
#include <category/execution/monad/graph_eval/types.hpp>

#include <cstdint>

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN


enum class Op : uint16_t
{
    Literal = 0,
    TensorRef,
    Add,
    Sub,
    Greater,
    Ge,
    Equal,
    Reshape,
    Where,
    CumSum,
    Saturate,
    MatMul,
    ArgMax,
    ArgMin,
    Clip,
    Max,
    Min,
    Mul,
    Div,
    Cast,
    Expand,
    Last_valid_op = Expand,
};

inline char const *op_name(Op const op)
{
    switch (op) {
    case Op::Literal:
        return "Literal";
    case Op::TensorRef:
        return "TensorRef";
    case Op::Add:
        return "Add";
    case Op::Sub:
        return "Sub";
    case Op::Greater:
        return "Greater";
    case Op::Ge:
        return "Ge";
    case Op::Equal:
        return "Equal";
    case Op::Reshape:
        return "Reshape";
    case Op::Where:
        return "Where";
    case Op::CumSum:
        return "CumSum";
    case Op::Saturate:
        return "Saturate";
    case Op::MatMul:
        return "MatMul";
    case Op::ArgMax:
        return "ArgMax";
    case Op::ArgMin:
        return "ArgMin";
    case Op::Clip:
        return "Clip";
    case Op::Max:
        return "Max";
    case Op::Min:
        return "Min";
    case Op::Mul:
        return "Mul";
    case Op::Div:
        return "Div";
    case Op::Cast:
        return "Cast";
    case Op::Expand:
        return "Expand";
    }
    MONAD_ABORT();
}


MONAD_GRAPH_EVAL_NAMESPACE_END
