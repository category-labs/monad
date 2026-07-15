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

MONAD_NAMESPACE_BEGIN

namespace outcome = BOOST_OUTCOME_V2_NAMESPACE;
namespace outcome_e = outcome::experimental;

template <typename T>
using StatusResult = outcome_e::status_result<T>;

template <typename T>
using Result = outcome::basic_outcome<T, typename StatusResult<T>::error_type, std::exception_ptr, typename StatusResult<T>::no_value_policy_type>;

template <typename T>
Result<T> result_from_status_result(StatusResult<T> r)
{
    return r.has_value() ? Result<T>{std::move(r).value()} : Result<T>{outcome::failure(std::move(r).error())};
}

MONAD_NAMESPACE_END
