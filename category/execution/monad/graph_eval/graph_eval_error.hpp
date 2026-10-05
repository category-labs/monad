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

#include "category/execution/monad/graph_eval/config.hpp"
#include <category/core/config.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_GRAPH_EVAL_NAMESPACE_BEGIN

enum class GraphEvalError
{
    Success = 0,
    MethodNotSupported,
    ValueNonZero,
    InvalidInput,
    ArityError,
    RankError,
    ShapeError,
    TypeError,
    InvalidOp,
    GraphValidationError,
    OutOfMemory,
    InternalError,
};

MONAD_GRAPH_EVAL_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::graph_eval::GraphEvalError>
    : quick_status_code_from_enum_defaults<monad::graph_eval::GraphEvalError>
{
    static constexpr auto const domain_name = "Graph Eval Error";
    // TODO: this UUID came to me in a dream
    static constexpr auto const domain_uuid =
        "cdddb691-e32d-4080-916d-47b773f88a37";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
