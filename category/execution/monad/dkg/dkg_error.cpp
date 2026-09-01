// Copyright (C) 2026 Category Labs, Inc.

#include <category/execution/monad/dkg/dkg_error.hpp>

#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::dkg::DkgError>::mapping> const &
quick_status_code_from_enum<monad::dkg::DkgError>::value_mappings()
{
    using monad::dkg::DkgError;
    static std::initializer_list<mapping> const values = {
        {DkgError::Success, "success", {errc::success}},
        {DkgError::MethodNotSupported, "method not supported", {}},
        {DkgError::ValueNonZero, "value is nonzero", {}},
        {DkgError::InvalidInput, "input is invalid", {}},
        {DkgError::InvalidPage, "invalid page", {}},
        {DkgError::RegistrationClosed, "registration is closed", {}},
        {DkgError::AlreadyRegistered, "validator is already registered", {}},
        {DkgError::NotValidator, "caller is not a validator", {}},
        {DkgError::EpochStateUnavailable, "epoch state is unavailable", {}},
        {DkgError::PartySetUnavailable, "party set is unavailable", {}},
        {DkgError::NotEpochParty, "caller is not an epoch party", {}},
        {DkgError::NotPcQcDealer, "caller is not the PC-QC dealer", {}},
        {DkgError::NotBveQcDealer, "caller is not the BVE-QC dealer", {}},
        {DkgError::PcQcRequired, "dealer has not posted a PC-QC", {}},
        {DkgError::DkgAlreadyFinished, "DKG is already finished", {}},
        {DkgError::ResultAlreadyRecorded, "DKG result is already recorded", {}},
        {DkgError::MalformedQc, "malformed DKG QC", {}},
        {DkgError::InvalidDkgResult, "invalid DKG result", {}},
        {DkgError::StakingLookupFailed, "staking lookup failed", {}},
        {DkgError::StateLimitExceeded, "native DKG state limit exceeded", {}},
    };
    return values;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
