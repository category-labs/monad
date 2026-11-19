// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/execution/domain/config.hpp>

#include <initializer_list>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

MONAD_DOMAIN_NAMESPACE_BEGIN

enum class DomainDerivationError
{
    Success = 0,
    // The domain has inputs, but its registration was never derived:
    // derivation started after it.
    NotRegistered,
    // The domain is registered again. The hub registers a domain once.
    AlreadyRegistered,
    // The domain db has blocks the hub has not recorded, so it does not belong
    // to this L1 chain.
    AheadOfHub,
};

MONAD_DOMAIN_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::domain::DomainDerivationError>
    : quick_status_code_from_enum_defaults<monad::domain::DomainDerivationError>
{
    static constexpr auto const domain_name = "Domain Derivation Error";
    static constexpr auto const domain_uuid =
        "7d0c5f0e-2a53-4f2b-9d0e-6c1b6f4a9e35";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
