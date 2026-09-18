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
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
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

BlobSchedule MonadL2::get_blob_schedule(uint64_t const timestamp) const
{
    if constexpr (l2_allows_l1_shape()) {
        // Diagnostic only, and it is not enough that both arms agree here --
        // without it both REFUSE, and a differential needs two roots to
        // compare.
        //
        // MONAD_BLOB_SCHEDULE keeps Cancun's update fraction, and a blob base
        // fee is exponential in excess_blob_gas over that fraction. A mainnet
        // Osaka header carries an excess_blob_gas scaled to the BPO2 fraction,
        // which is 3.5x larger; read against Cancun's it comes out around
        // 1e23 wei, so every blob transaction fails
        // static_validate_transaction's max_fee_per_blob_gas test and takes
        // its block with it. Measured on the corpus: excess_blob_gas
        // 176,746,387 gives 9.8e22 against Cancun's fraction and 3,709,274
        // against BPO2's.
        //
        // So the L1 rule is used for an L1 block, which is what this lever
        // means everywhere else too. Delegated rather than transcribed: a
        // second copy of that timestamp ladder would be one more thing to
        // keep in step with a fork schedule this chain otherwise ignores.
        return EthereumMainnet{}.get_blob_schedule(timestamp);
    }
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
