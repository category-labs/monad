// Copyright (C) 2026 Category Labs, Inc.
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

#include <zkvm/guest/monad_l2_chain.hpp>

#include <category/core/assert.h>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <zkvm/guest/l2_config.hpp>

MONAD_NAMESPACE_BEGIN

uint256_t MonadL2::get_chain_id() const
{
    return uint256_t{L2_CHAIN_ID};
}

monad_eth_revision MonadL2::get_revision(uint64_t, uint64_t) const
{
    // Both arguments are ignored, and that is the point: there is no schedule.
    return L2_REVISION;
}

BlobSchedule MonadL2::get_blob_schedule(uint64_t) const
{
    // Read per transaction, so it has to be a real value. Zero limits mean a
    // blob transaction is rejected, which is what an L2 without blobs wants,
    // and the nonzero update fraction is there because the shared transaction
    // context computes a blob base fee unconditionally.
    return MONAD_BLOB_SCHEDULE;
}

GenesisState MonadL2::get_genesis_state() const
{
    // Unreachable by construction: genesis loading goes through TrieDb, whose
    // translation unit the guest build drops. Saying so loudly beats returning
    // an empty GenesisState, which would be a silently mainnet-shaped answer.
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END
