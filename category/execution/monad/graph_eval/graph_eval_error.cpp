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

#include <category/execution/monad/graph_eval/graph_eval_error.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<quick_status_code_from_enum<
    monad::graph_eval::GraphEvalError>::mapping> const &
quick_status_code_from_enum<monad::graph_eval::GraphEvalError>::value_mappings()
{
    using monad::graph_eval::GraphEvalError;

    static std::initializer_list<mapping> const v = {
        {GraphEvalError::Success, "success", {errc::success}},
        {GraphEvalError::MethodNotSupported, "method not supported", {}},
        {GraphEvalError::ValueNonZero, "value is nonzero", {}},
        {GraphEvalError::InvalidInput, "input is invalid", {}},
        {GraphEvalError::ArityError, "wrong number of inputs", {}},
        {GraphEvalError::RankError, "tensor rank is invalid", {}},
        {GraphEvalError::ShapeError, "tensor shape is invalid", {}},
        {GraphEvalError::TypeError, "tensor dtype is invalid", {}},
        {GraphEvalError::InvalidOp, "op is invalid", {}},
        {GraphEvalError::GraphValidationError, "graph is invalid", {}},
        {GraphEvalError::OutOfMemory, "graph needs too much memory", {}},
        {GraphEvalError::InternalError, "internal error", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
