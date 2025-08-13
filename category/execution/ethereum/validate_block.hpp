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
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/core/result.hpp>

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
#include <vector>

MONAD_NAMESPACE_BEGIN

enum class BlockError
{
    Success = 0,
    GasAboveLimit,
    InvalidGasLimit,
    ExtraDataTooLong,
    WrongOmmersHash,
    WrongParentHash,
    FieldBeforeFork,
    MissingField,
    PowBlockAfterMerge,
    InvalidNonce,
    TooManyOmmers,
    DuplicateOmmers,
    InvalidOmmerHeader,
    WrongDaoExtraData,
    WrongLogsBloom,
    InvalidGasUsed,
    WrongMerkleRoot
};

struct Block;
struct BlockHeader;

Receipt::Bloom compute_bloom(std::vector<Receipt> const &);

bytes32_t compute_ommers_hash(std::vector<BlockHeader> const &);

template <evmc_revision rev>
Result<void> static_validate_header(BlockHeader const &);

template <evmc_revision rev>
Result<void> static_validate_block(Block const &);

Result<void> static_validate_block(evmc_revision, Block const &);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

template <>
struct quick_status_code_from_enum<monad::BlockError>
    : quick_status_code_from_enum_defaults<monad::BlockError>
{
    static constexpr auto const domain_name = "Block Error";
    static constexpr auto const domain_uuid =
        "6eb636da00ddd479646eeb39b8168c814cb4";

    static std::initializer_list<mapping> const &value_mappings();
};

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
