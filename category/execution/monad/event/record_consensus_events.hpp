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
#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

/// Record the BLOCK_QC event, using the QC for the parent block that is
/// presented in a newly proposed block's header
template <class MonadConsensusBlockHeader>
void record_block_qc(
    MonadConsensusBlockHeader const &, uint64_t finalized_block_num);

/// Record the BLOCK_FINALIZED event
void record_block_finalized(bytes32_t const &block_id, uint64_t block_number);

/// Record a BLOCK_VERIFIED event for each of the given block numbers
void record_block_verified(std::span<uint64_t const> verified_blocks);

MONAD_NAMESPACE_END
