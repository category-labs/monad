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

#include <category/execution/domain/derivation_error.hpp>

#include <initializer_list>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<quick_status_code_from_enum<
    monad::domain::DomainDerivationError>::mapping> const &
quick_status_code_from_enum<
    monad::domain::DomainDerivationError>::value_mappings()
{
    using monad::domain::DomainDerivationError;

    static std::initializer_list<mapping> const mappings = {
        {DomainDerivationError::Success, "success", {errc::success}},
        {DomainDerivationError::NotRegistered,
         "the domain has inputs before its registration was derived",
         {}},
        {DomainDerivationError::AlreadyRegistered,
         "the domain is registered again",
         {}},
        {DomainDerivationError::AheadOfHub,
         "the domain has blocks the hub has not recorded",
         {}}};
    return mappings;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
