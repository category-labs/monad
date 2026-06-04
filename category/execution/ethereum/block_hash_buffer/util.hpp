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

#pragma once

#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class BlockDb;
class BlockHashBufferFinalized;

namespace mpt
{
    class Db;
}

// Populate `block_hash_buffer` with up to 256 ancestor hashes preceding
// `block_number` sourced from a TrieDb instance.
bool init_block_hash_buffer_from_triedb(
    mpt::Db const &, uint64_t, BlockHashBufferFinalized &);

// Populate `block_hash_buffer` with up to 256 ancestor hashes preceding
// `block_number` sourced from a BlockDb instance.
bool init_block_hash_buffer_from_blockdb(
    BlockDb const &, uint64_t block_number, BlockHashBufferFinalized &);

MONAD_NAMESPACE_END
