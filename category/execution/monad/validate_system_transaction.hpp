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

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/outcome/config.hpp>
// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif
#include <boost/outcome/success_failure.hpp>

#include <initializer_list>

MONAD_NAMESPACE_BEGIN

enum class SystemTransactionError
{
    Success = 0,
    SystemTxnBeforeFork,
    GasNonZero,
    ValueNonZero,
    TypeNotLegacy,
    BadSender,
    MissingTo,
    InvalidSystemContract,
    NonEmptyAuthorizationList,
};

struct Transaction;

template <Traits traits>
Result<void> static_validate_system_transaction(
    Transaction const &tx, Address const &sender);

Result<void> validate_system_transaction(
    Transaction const &, std::optional<Account> const &sender_account);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::SystemTransactionError>
    : quick_status_code_from_enum_defaults<monad::SystemTransactionError>
{
    static constexpr auto const domain_name = "System Transaction Error";
    static constexpr auto const domain_uuid =
        "2cf70992-50f3-4583-8100-3e662c79dbb0";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
