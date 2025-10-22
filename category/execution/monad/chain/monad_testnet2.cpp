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
#include <category/execution/monad/chain/monad_testnet2.hpp>
#include <category/execution/monad/chain/monad_testnet2_alloc.hpp>
#include <category/vm/evm/monad/revision.h>

MONAD_NAMESPACE_BEGIN

monad_revision MonadTestnet2::get_monad_revision(uint64_t const timestamp) const
{
    if (MONAD_LIKELY(timestamp >= 1761312600)) { // 2025-10-24T13:30:00.000Z
        return MONAD_FIVE;
    }
    else if (timestamp >= 1758029400) { // 2025-09-16T13:30:00.000Z
        return MONAD_FOUR;
    }
    return MONAD_THREE;
}

uint256_t MonadTestnet2::get_chain_id() const
{
    return 30143;
};

GenesisState MonadTestnet2::get_genesis_state() const
{
    BlockHeader header;
    header.gas_limit = 5000;
    header.extra_data = evmc::from_hex("0x0000000000000000000000000000000000000"
                                       "000000000000000000000000000")
                            .value();
    header.base_fee_per_gas = 0;
    header.withdrawals_root = NULL_ROOT;
    header.blob_gas_used = 0;
    header.excess_blob_gas = 0;
    header.parent_beacon_block_root = NULL_ROOT;
    return {header, MONAD_TESTNET2_ALLOC};
}

MONAD_NAMESPACE_END
