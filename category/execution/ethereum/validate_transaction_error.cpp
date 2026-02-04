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

#include <category/execution/ethereum/validate_transaction_error.hpp>

#include <boost/outcome/config.hpp>
// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif
#include <boost/outcome/success_failure.hpp>

#include <initializer_list>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::TransactionError>::mapping> const &
quick_status_code_from_enum<monad::TransactionError>::value_mappings()
{
    using monad::TransactionError;

    static std::initializer_list<mapping> const v = {
        {TransactionError::Success, "success", {errc::success}},
        {TransactionError::InsufficientBalance, "insufficient balance", {}},
        {TransactionError::IntrinsicGasGreaterThanLimit,
         "intrinsic gas greater than limit",
         {}},
        {TransactionError::BadNonce, "bad nonce", {}},
        {TransactionError::SenderNotEoa, "sender not eoa", {}},
        {TransactionError::TypeNotSupported, "type not supported", {}},
        {TransactionError::MaxFeeLessThanBase, "max fee less than base", {}},
        {TransactionError::PriorityFeeGreaterThanMax,
         "priority fee greater than max",
         {}},
        {TransactionError::NonceExceedsMax, "nonce exceeds max", {}},
        {TransactionError::InitCodeLimitExceeded,
         "init code limit exceeded",
         {}},
        {TransactionError::GasLimitReached, "gas limit reached", {}},
        {TransactionError::WrongChainId, "wrong chain id", {}},
        {TransactionError::MissingSender, "missing sender", {}},
        {TransactionError::GasLimitOverflow, "gas limit overflow", {}},
        {TransactionError::InvalidSignature, "invalid signature", {}},
        {TransactionError::InvalidBlobHash, "invalid blob hash", {}},
        {TransactionError::EmptyAuthorizationList,
         "empty authorization list",
         {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
