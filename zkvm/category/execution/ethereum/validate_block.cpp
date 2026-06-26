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

// zkVM shadow of validate_block.cpp. The host TU is dropped from the guest
// build (fiber dispatch, live-DB header validation), but the guest still
// references the BlockError status-code domain: execute_block_zkvm returns
// BlockError::InvalidRequestsHash and ffi.cpp returns BlockError::
// FieldBeforeFork. Provide just the value_mappings() out-of-line definition
// that backs that domain; everything else lives in the (header-declared)
// quick_status_code_from_enum specialization.

#include <category/execution/ethereum/validate_block.hpp>

#include <initializer_list>

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::BlockError>::mapping> const &
quick_status_code_from_enum<monad::BlockError>::value_mappings()
{
    using monad::BlockError;

    static std::initializer_list<mapping> const v = {
        {BlockError::Success, "success", {errc::success}},
        {BlockError::GasAboveLimit, "gas above limit", {}},
        {BlockError::InvalidGasLimit, "invalid gas limit", {}},
        {BlockError::ExtraDataTooLong, "extra data too long", {}},
        {BlockError::WrongOmmersHash, "wrong ommers hash", {}},
        {BlockError::WrongParentHash, "wrong parent hash", {}},
        {BlockError::FieldBeforeFork, "field before fork", {}},
        {BlockError::MissingField, "missing field", {}},
        {BlockError::PowBlockAfterMerge, "pow block after merge", {}},
        {BlockError::InvalidNonce, "invalid nonce", {}},
        {BlockError::TooManyOmmers, "too many ommers", {}},
        {BlockError::DuplicateOmmers, "duplicate ommers", {}},
        {BlockError::InvalidOmmerHeader, "invalid ommer header", {}},
        {BlockError::WrongLogsBloom, "wrong logs bloom", {}},
        {BlockError::InvalidGasUsed, "invalid gas used", {}},
        {BlockError::WrongMerkleRoot, "wrong merkle root", {}},
        {BlockError::SystemCallMissingCode,
         "system call target has no code",
         {}},
        {BlockError::SystemCallFailed, "system call failed", {}},
        {BlockError::InvalidRequestsHash, "invalid requests hash", {}},
        {BlockError::InvalidDepositLog, "invalid deposit log", {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
