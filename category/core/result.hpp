// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/config.hpp>

#include <boost/outcome.hpp>
#include <boost/outcome/experimental/status_result.hpp>

#include <exception>

MONAD_NAMESPACE_BEGIN

namespace outcome = BOOST_OUTCOME_V2_NAMESPACE;
namespace outcome_e = outcome::experimental;

template <typename T>
using Result = outcome_e::status_result<T>;

template <typename T>
using Outcome =
    outcome::outcome<T, typename Result<T>::error_type, std::exception_ptr>;

template <typename T>
Outcome<T> outcome_from_result(Result<T> res)
{
    if (res.has_error()) {
        return std::move(res).as_failure();
    }
    return std::move(res).assume_value();
}

template <typename T>
Result<T> result_from_outcome_or_throw(Outcome<T> out)
{
    if (out.has_exception()) {
        std::rethrow_exception(out.exception());
    }
    if (out.has_error()) {
        return std::move(out).assume_error();
    }
    return std::move(out).assume_value();
}

MONAD_NAMESPACE_END
