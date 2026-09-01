// Copyright (C) 2026 Category Labs, Inc.

#pragma once

#include <category/core/config.hpp>

#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>

MONAD_NAMESPACE_BEGIN

namespace dkg
{

    enum class DkgError
    {
        Success = 0,
        MethodNotSupported,
        ValueNonZero,
        InvalidInput,
        InvalidPage,
        RegistrationClosed,
        AlreadyRegistered,
        NotValidator,
        EpochStateUnavailable,
        PartySetUnavailable,
        NotEpochParty,
        NotPcQcDealer,
        NotBveQcDealer,
        PcQcRequired,
        DkgAlreadyFinished,
        ResultAlreadyRecorded,
        MalformedQc,
        InvalidDkgResult,
        StakingLookupFailed,
        StateLimitExceeded,
    };

} // namespace dkg

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::dkg::DkgError>
    : quick_status_code_from_enum_defaults<monad::dkg::DkgError>
{
    static constexpr auto const domain_name = "Native DKG Contract Error";
    static constexpr auto const domain_uuid =
        "98868f8c-14ec-4e6e-847e-4c860886195b";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
