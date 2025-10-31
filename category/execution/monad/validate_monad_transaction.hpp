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

#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/evm/monad/revision.h>

#include <evmc/evmc.h>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif

#include <initializer_list>
#include <optional>
#include <span>

MONAD_NAMESPACE_BEGIN

struct Transaction;
class State;

enum class MonadTransactionError
{
    Success = 0,
    InsufficientBalanceForFee, ///< Account doesn't have enough balance to pay
                               ///< transaction fees
    SystemTransactionSenderIsAuthority,
};

Result<void> validate_monad_transaction(
    monad_revision, evmc_revision, Transaction const &, Address const &sender,
    State &, uint256_t const &base_fee_per_gas,
    std::span<std::optional<Address> const> authorities);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::MonadTransactionError>
    : quick_status_code_from_enum_defaults<monad::MonadTransactionError>
{
    static constexpr auto const domain_name = "Monad Transaction Error";
    static constexpr auto const domain_uuid =
        "3f33419a9e8e4f14fcc2fc2ff439eb23e391";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
