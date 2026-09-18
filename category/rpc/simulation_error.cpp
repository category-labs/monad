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

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/rpc/simulation_error.hpp>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
    #include <boost/outcome/experimental/status-code/status-code/quick_status_code_from_enum.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/quick_status_code_from_enum.hpp>
#endif
#include <evmc/evmc.h>

#include <initializer_list>
#include <string>

MONAD_NAMESPACE_BEGIN

namespace
{
    evmc_status_code simulation_status(SimulationError const error)
    {
        switch (error) {
        case SimulationError::Success:
            return EVMC_SUCCESS;
        case SimulationError::InvalidInput:
        case SimulationError::InvalidData:
        case SimulationError::WithdrawalsNotSupported:
        case SimulationError::BlockNumbersNotIncreasing:
        case SimulationError::BlockTimestampsNotMonotonic:
        case SimulationError::SimulationHeaderNotAfterBase:
        case SimulationError::TransactionsContextUnavailable:
        case SimulationError::InvalidBlockGap:
        case SimulationError::GasLimitExceeded:
        case SimulationError::StateOverrideFailure:
        case SimulationError::InternalError:
            return EVMC_INTERNAL_ERROR;
        }
        return EVMC_INTERNAL_ERROR;
    }

    evmc_status_code block_status(BlockError const error)
    {
        switch (error) {
        case BlockError::Success:
            return EVMC_SUCCESS;
        case BlockError::GasAboveLimit:
        case BlockError::InvalidGasLimit:
        case BlockError::ExtraDataTooLong:
        case BlockError::WrongOmmersHash:
        case BlockError::WrongParentHash:
        case BlockError::FieldBeforeFork:
        case BlockError::MissingField:
        case BlockError::PowBlockAfterMerge:
        case BlockError::InvalidNonce:
        case BlockError::TooManyOmmers:
        case BlockError::DuplicateOmmers:
        case BlockError::InvalidOmmerHeader:
        case BlockError::WrongLogsBloom:
        case BlockError::InvalidGasUsed:
        case BlockError::InvalidExcessBlobGas:
        case BlockError::WrongMerkleRoot:
        case BlockError::SystemCallMissingCode:
        case BlockError::SystemCallFailed:
        case BlockError::InvalidRequestsHash:
        case BlockError::InvalidDepositLog:
            return EVMC_REJECTED;
        }
        return EVMC_INTERNAL_ERROR;
    }
}

SimulationErrorInfo simulation_error_info(Result<void>::error_type const &error)
{
    static Result<void>::error_type const simulation_error =
        SimulationError::GasLimitExceeded;
    static Result<void>::error_type const block_error =
        BlockError::GasAboveLimit;

    evmc_status_code status_code = EVMC_REJECTED;
    if (error.domain() == simulation_error.domain()) {
        status_code =
            simulation_status(static_cast<SimulationError>(error.value()));
    }
    else if (error.domain() == block_error.domain()) {
        status_code = block_status(static_cast<BlockError>(error.value()));
    }

    return SimulationErrorInfo{
        .status_code = status_code,
        .message = std::string{error.message().c_str()},
    };
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::SimulationError>::mapping> const &
quick_status_code_from_enum<monad::SimulationError>::value_mappings()
{
    using monad::SimulationError;

    static std::initializer_list<mapping> const v = {
        {SimulationError::Success, "success", {errc::success}},
        {SimulationError::InvalidInput, "invalid input", {}},
        {SimulationError::InvalidData, "invalid data", {}},
        {SimulationError::WithdrawalsNotSupported,
         "Withdrawals are not supported on Monad",
         {}},
        {SimulationError::BlockNumbersNotIncreasing,
         "block numbers must be strictly increasing",
         {}},
        {SimulationError::BlockTimestampsNotMonotonic,
         "block timestamps must be monotonically increasing",
         {}},
        {SimulationError::SimulationHeaderNotAfterBase,
         "simulation header number must be greater than the base header "
         "number",
         {}},
        {SimulationError::TransactionsContextUnavailable,
         "failed to recover the transactions context",
         {}},
        {SimulationError::InvalidBlockGap,
         "the block gap must be exactly 1 after filling in synthetic blocks",
         {}},
        {SimulationError::GasLimitExceeded, "gas limit exceeded", {}},
        {SimulationError::StateOverrideFailure,
         "failed to apply state override",
         {}},
        {SimulationError::InternalError, "internal error", {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
