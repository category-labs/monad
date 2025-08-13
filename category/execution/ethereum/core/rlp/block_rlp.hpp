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
#include <category/execution/ethereum/core/block.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_block_header(BlockHeader const &);
byte_string encode_block(Block const &);
byte_string encode_ommers(std::vector<BlockHeader> const &);

Result<Block> decode_block(byte_string_view &);
Result<BlockHeader> decode_block_header(byte_string_view &);
Result<std::vector<BlockHeader>>
decode_block_header_vector(byte_string_view &enc);

MONAD_RLP_NAMESPACE_END
