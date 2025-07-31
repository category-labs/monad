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
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>

#include <initializer_list>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_NAMESPACE_BEGIN

enum class MathError
{
    Success = 0,
    Overflow,
    Underflow,
    DivisionByZero,
};

Result<uint256_t> checked_add(uint256_t const &x, uint256_t const &y);
Result<uint256_t> checked_sub(uint256_t const &x, uint256_t const &y);
Result<uint256_t> checked_mul(uint256_t const &x, uint256_t const &y);
Result<uint256_t> checked_div(uint256_t const &x, uint256_t const &y);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::MathError>
    : quick_status_code_from_enum_defaults<monad::MathError>
{
    static constexpr auto const domain_name = "Math Error";
    static constexpr auto const domain_uuid =
        "b9042736-4854-46e9-bafe-f168aab34de9";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
