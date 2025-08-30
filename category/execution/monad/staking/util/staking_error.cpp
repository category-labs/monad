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

#include <category/execution/monad/staking/util/staking_error.hpp>

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

std::initializer_list<
    quick_status_code_from_enum<monad::staking::StakingError>::mapping> const &
quick_status_code_from_enum<monad::staking::StakingError>::value_mappings()
{
    using monad::staking::StakingError;

    static std::initializer_list<mapping> const v = {
        {StakingError::Success, "success", {errc::success}},
        {StakingError::InternalError, "internal error", {}},
        {StakingError::MethodNotSupported, "method not supported", {}},
        {StakingError::InvalidInput, "invalid input", {}},
        {StakingError::ValidatorExists, "validator exists", {}},
        {StakingError::UnknownValidator, "unknown validator", {}},
        {StakingError::UnknownDelegator, "unknown delegator", {}},
        {StakingError::WithdrawalIdExists, "withdrawal id exists", {}},
        {StakingError::UnknownWithdrawalId, "unknown withdrawal id", {}},
        {StakingError::WithdrawalNotReady, "withdrawal not ready", {}},
        {StakingError::InsufficientStake, "insufficient stake", {}},
        {StakingError::InvalidSecpPubkey, "invalid secp pubkey", {}},
        {StakingError::InvalidBlsPubkey, "invalid bls pubkey", {}},
        {StakingError::InvalidSecpSignature, "invalid secp signature", {}},
        {StakingError::InvalidBlsSignature, "invalid bls signature", {}},
        {StakingError::SecpSignatureVerificationFailed,
         "secp signature verification failed",
         {}},
        {StakingError::BlsSignatureVerificationFailed,
         "bls signature verification failed",
         {}},
        {StakingError::BlockAuthorNotInSet, "block author not in set", {}},
        {StakingError::SolvencyError, "solvency error", {}},
        {StakingError::SnapshotInBoundary,
         "called snapshot while in boundary",
         {}},
        {StakingError::InvalidEpochChange, "invalid epoch change", {}},
        {StakingError::RequiresAuthAddress, "requires auth address", {}},
        {StakingError::CommissionTooHigh, "commission too high", {}},
        {StakingError::ValueNonZero, "value is nonzero", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
