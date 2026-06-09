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

#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/hive_net.hpp>
#include <category/execution/ethereum/chain/hive_net_alloc.hpp>

MONAD_NAMESPACE_BEGIN

uint256_t HiveNet::get_chain_id() const
{
    return 3503995874084926;
}

// Fork schedule from the Hive runner tests. Monad execution currently supports
// Berlin and later, so the fixture activates earlier forks as Berlin.
monad_eth_revision HiveNet::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    if (block_number >= 36) {
        if (timestamp >= 450) {
            return MONAD_ETH_PRAGUE;
        }
        if (timestamp >= 420) {
            return MONAD_ETH_CANCUN;
        }
        if (timestamp >= 390) {
            return MONAD_ETH_SHANGHAI;
        }
        return MONAD_ETH_PARIS;
    }
    if (block_number >= 27) {
        return MONAD_ETH_LONDON;
    }
    return MONAD_ETH_BERLIN;
}

BlobSchedule HiveNet::get_blob_schedule(uint64_t const timestamp) const
{
    if (timestamp >= 450) {
        return PRAGUE_BLOB_SCHEDULE;
    }
    return CANCUN_BLOB_SCHEDULE;
}

GenesisState HiveNet::get_genesis_state() const
{
    BlockHeader header;
    header.difficulty = 0x20000;
    header.gas_limit = 0x5f5e100;
    store_be(header.nonce.data(), uint64_t{0x0});
    header.extra_data = from_hex("0x68697665636861696e").value();
    return {header, HIVE_NET_ALLOC};
}

MONAD_NAMESPACE_END
