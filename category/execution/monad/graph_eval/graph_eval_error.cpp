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

    // Every error has the same message. A failed precompile call reverts with
    // its error's message as the revert data (check_call_monad_precompile), so
    // the revert data doesn't identify the failure condition. Calldata too
    // short for the shared ABI helpers fails with AbiDecodeError::InputTooShort
    // instead, and reverts with that error's message
    //
    // TODO: consider standardizing on a small set of visible messages
    static std::initializer_list<mapping> const v = {
        {GraphEvalError::Success, "success", {errc::success}},
        {GraphEvalError::MethodNotSupported, "graph eval error", {}},
        {GraphEvalError::ValueNonZero, "graph eval error", {}},
        {GraphEvalError::InvalidInput, "graph eval error", {}},
        {GraphEvalError::ArityError, "graph eval error", {}},
        {GraphEvalError::RankError, "graph eval error", {}},
        {GraphEvalError::ShapeError, "graph eval error", {}},
        {GraphEvalError::TypeError, "graph eval error", {}},
        {GraphEvalError::InvalidOp, "graph eval error", {}},
        {GraphEvalError::GraphValidationError, "graph eval error", {}},
        {GraphEvalError::OutOfMemory, "graph eval error", {}},
        {GraphEvalError::InternalError, "graph eval error", {}},
        {GraphEvalError::DivisionByZero, "graph eval error", {}},
        {GraphEvalError::DomainError, "graph eval error", {}},
        {GraphEvalError::InvalidTensorRef, "graph eval error", {}},
        {GraphEvalError::IndexError, "graph eval error", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
