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

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>

#include <initializer_list>

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

static_assert(noexcept(Result<uint256_t>{uint256_t{}}));
static_assert(noexcept(Result<uint256_t>{MathError::Overflow}));

Result<uint256_t> checked_add(uint256_t const &x, uint256_t const &y) noexcept
{
    // addc captures the carry directly; avoids a separate 256-bit comparison.
    auto const [sum, carry] = addc(x, y);
    if (MONAD_UNLIKELY(carry)) {
        return MathError::Overflow;
    }
    return sum;
}

Result<uint256_t> checked_sub(uint256_t const &x, uint256_t const &y) noexcept
{
    // subb captures the borrow directly; avoids a separate 256-bit comparison.
    auto const [diff, borrow] = subb(x, y);
    if (MONAD_UNLIKELY(borrow)) {
        return MathError::Underflow;
    }
    return diff;
}

Result<uint256_t> checked_mul(uint256_t const &x, uint256_t const &y) noexcept
{
    // Compute the full 512-bit product; overflow iff any upper word is set.
    auto const prod =
        truncating_mul<2 * uint256_t::num_words>(x.as_words(), y.as_words());
    if (MONAD_UNLIKELY((prod[4] | prod[5] | prod[6] | prod[7]) != 0)) {
        return MathError::Overflow;
    }
    return uint256_t{
        std::array<uint64_t, 4>{prod[0], prod[1], prod[2], prod[3]}};
}

Result<uint256_t> checked_div(uint256_t const &x, uint256_t const &y) noexcept
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
