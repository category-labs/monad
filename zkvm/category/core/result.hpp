// Copyright (C) 2025-26 Category Labs, Inc.
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

// zkVM shadow of category/core/result.hpp. The host uses
// outcome::experimental::status_result<T>, whose default NoValuePolicy is
// status_code_throw — its wide_value_check contains a literal `throw`
// statement that won't compile under -fno-exceptions ("instantiating
// erroneous template" once the type is referenced anywhere).
//
// Swap the policy to outcome::policy::terminate: .value() on an error
// state calls std::terminate(), which (via our abort() stub in
// zkvm/core/libstdcxx.cpp) routes to zkvm_halt(1) — a clean failed-proof
// halt instead of an exception.

#pragma once

#include <category/core/config.hpp>

// boost/outcome 1.x's status_result.hpp::status_code_throw::wide_value_check
// expands BOOST_OUTCOME_THROW_EXCEPTION("...") with a string literal when
// BOOST_NO_EXCEPTIONS is defined (i.e. -fno-exceptions). The macro chains to
// boost::throw_exception(char const *, source_location), but the only
// declared overloads take std::exception const &. Override the macro to
// std::abort() before the boost include so the constexpr body parses.
// We never reach this path at runtime because Result uses policy::terminate.
#include <cstdlib>
#ifndef BOOST_OUTCOME_THROW_EXCEPTION
    #define BOOST_OUTCOME_THROW_EXCEPTION(expr) std::abort()
#endif

#include <boost/outcome/experimental/status_result.hpp>
#include <boost/outcome/policy/terminate.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

namespace outcome = BOOST_OUTCOME_V2_NAMESPACE;
namespace outcome_e = outcome::experimental;

template <typename T>
using Result = outcome_e::status_result<
    T,
    outcome_e::errored_status_code<::system_error2::detail::erased<intptr_t>>,
    outcome::policy::terminate>;

MONAD_NAMESPACE_END
