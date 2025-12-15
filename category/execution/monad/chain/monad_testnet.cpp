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

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/chain/monad_testnet_alloc.hpp>
#include <category/vm/evm/monad/revision.h>

MONAD_NAMESPACE_BEGIN

monad_revision MonadTestnet::get_monad_revision(uint64_t const timestamp) const
{
    if (MONAD_LIKELY(timestamp >= 1763562600)) { // 2025-11-19T14:30:00.000Z
        return MONAD_EIGHT;
    }
    if (timestamp >= 1762353000) { // 2025-11-05T14:30:00.000Z
        return MONAD_SEVEN;
    }
    if (timestamp >= 1761917400) { // 2025-10-31T13:30:00.000Z
        return MONAD_SIX;
    }
    else if (timestamp >= 1761658200) { // 2025-10-28T13:30:00.000Z
        return MONAD_FIVE;
    }
    else if (timestamp >= 1760448600) { // 2025-10-14T13:30:00.000Z
        return MONAD_FOUR;
    }
    else if (timestamp >= 1755005400) { // 2025-08-12T13:30:00.000Z
        return MONAD_THREE;
    }
    else if (timestamp >= 1741978800) { // 2025-03-14T19:00:00.000Z
        return MONAD_TWO;
    }
    else if (timestamp >= 1739559600) { // 2025-02-14T19:00:00.000Z
        return MONAD_ONE;
    }
    return MONAD_ZERO;
}

uint256_t MonadTestnet::get_chain_id() const
{
    return 10143;
};

GenesisState MonadTestnet::get_genesis_state() const
{
    BlockHeader const header{
        .gas_limit = 5000,
        .extra_data = evmc::from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                                     "db3db69cbdb7a38e1e50b1b82fa")
                          .value(),
        .base_fee_per_gas = 0,
        .withdrawals_root = NULL_ROOT,
        .blob_gas_used = 0,
        .excess_blob_gas = 0,
        .parent_beacon_block_root = NULL_ROOT,
        .requests_hash = NULL_HASH,
    };
    return {header, MONAD_TESTNET_ALLOC};
}

MONAD_NAMESPACE_END
