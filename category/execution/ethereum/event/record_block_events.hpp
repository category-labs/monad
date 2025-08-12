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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/block.hpp>

#include <cstddef>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

/// Named pair holding the Ethereum block execution outputs
struct BlockExecOutput
{
    BlockHeader eth_header;
    bytes32_t eth_block_hash;
};

/// Record the start of block execution: emits a BLOCK_START event and sets the
/// global block flow sequence number in the recorder
void record_block_exec_start(
    bytes32_t const &bft_block_id, uint256_t const &chain_id,
    bytes32_t const &eth_parent_hash, BlockHeader const &, uint64_t block_round,
    uint64_t epoch, size_t txn_count);

/// Record block execution output events (or an execution error event, if
/// Result::has_error() is true); also clears the active block flow ID
Result<BlockExecOutput> record_block_exec_result(Result<BlockExecOutput>);

MONAD_NAMESPACE_END
