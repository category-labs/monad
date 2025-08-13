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

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/monad/core/monad_block.hpp>

MONAD_RLP_NAMESPACE_BEGIN

Result<uint64_t> decode_consensus_block_header_timestamp_s(byte_string_view &);
Result<MonadConsensusBlockBody> decode_consensus_block_body(byte_string_view &);
template <class MonadConsensusBlockHeader>
Result<MonadConsensusBlockHeader>
decode_consensus_block_header(byte_string_view &);

MONAD_RLP_NAMESPACE_END
