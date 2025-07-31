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

#include <category/execution/ethereum/core/contract/checked_math.hpp>

#include <boost/outcome/config.hpp>
// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif

MONAD_NAMESPACE_BEGIN

Result<uint256_t> checked_add(uint256_t const &x, uint256_t const &y)
{
    auto const res = intx::addc(x, y);
    if (MONAD_UNLIKELY(res.carry)) {
        return MathError::Overflow;
    }
    return res.value;
}

Result<uint256_t> checked_sub(uint256_t const &x, uint256_t const &y)
{
    auto const res = intx::subc(x, y);
    if (MONAD_UNLIKELY(res.carry)) {
        return MathError::Underflow;
    }
    return res.value;
}

Result<uint256_t> checked_mul(uint256_t const &x, uint256_t const &y)
{
    uint512_t const z = intx::umul(x, y);
    if (MONAD_UNLIKELY((z > UINT256_MAX))) {
        return MathError::Overflow;
    }
    return static_cast<uint256_t>(z);
}

Result<uint256_t> checked_div(uint256_t const &x, uint256_t const &y)
{
    if (y == 0) {
        return MathError::DivisionByZero;
    }
    return x / y;
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::MathError>::mapping> const &
quick_status_code_from_enum<monad::MathError>::value_mappings()
{
    using monad::MathError;

    static std::initializer_list<mapping> const v = {
        {MathError::Success, "success", {errc::success}},
        {MathError::Overflow, "overflow", {}},
        {MathError::Underflow, "underflow", {}},
        {MathError::DivisionByZero, "division by zero", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
