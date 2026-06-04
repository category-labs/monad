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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/log.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_buffer/util.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

bool init_block_hash_buffer_from_triedb(
    mpt::Db const &rodb, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer)
{
    for (uint64_t b = block_number < 256 ? 0 : block_number - 256;
         b < block_number;
         ++b) {
        auto const header = rodb.find(
            mpt::concat(
                FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
            b);
        if (!header.has_value()) {
            LOG_WARNING(
                "Could not query block header {} from TrieDb -- {}",
                b,
                header.error().message().c_str());
            return false;
        }
        auto const h = to_bytes(keccak256(header.value().node->value()));
        block_hash_buffer.set(b, h);
    }

    return true;
}

bool init_block_hash_buffer_from_blockdb(
    BlockDb const &block_db, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer)
{
    for (uint64_t b = block_number < 256 ? 1 : block_number - 255;
         b <= block_number;
         ++b) {
        Block block;
        auto const ok = block_db.get(b, block);
        if (!ok) {
            LOG_WARNING("Could not query block {} from blockdb.", b);
            return false;
        }
        block_hash_buffer.set(b - 1, block.header.parent_hash);
    }

    return true;
}

MONAD_NAMESPACE_END
