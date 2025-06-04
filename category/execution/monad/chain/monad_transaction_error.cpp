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

#include <category/execution/monad/chain/monad_transaction_error.hpp>

#include <system_error>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::MonadTransactionError>::mapping> const &
quick_status_code_from_enum<monad::MonadTransactionError>::value_mappings()
{
    using monad::MonadTransactionError;

    static std::initializer_list<mapping> const v = {
        {MonadTransactionError::Success, "success", {errc::success}},
        {MonadTransactionError::InsufficientBalanceForFee,
         "insufficient balance for fee",
         {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
