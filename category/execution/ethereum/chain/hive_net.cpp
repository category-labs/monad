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
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/hive_net.hpp>
#include <category/execution/ethereum/chain/hive_net_alloc.hpp>

MONAD_NAMESPACE_BEGIN

uint256_t HiveNet::get_chain_id() const
{
    return 3503995874084926;
}

// Fork schedule from the Hive runner tests. The chain is merged from genesis
// (proof-of-stake, no pre-Berlin blocks): Berlin, London, Paris and Shanghai
// are all active at genesis (timestamp 0), Cancun activates at timestamp 30 and
// Prague at timestamp 60. Dispatch is therefore purely by timestamp.
monad_eth_revision HiveNet::get_revision(
    uint64_t const /*block_number*/, uint64_t const timestamp) const
{
    if (timestamp >= 60) {
        return MONAD_ETH_PRAGUE;
    }
    if (timestamp >= 30) {
        return MONAD_ETH_CANCUN;
    }
    return MONAD_ETH_SHANGHAI;
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
    // London and Shanghai are active at genesis, so the genesis header
    // carries a base fee of 1 Gwei and an empty withdrawals root; without
    // them the genesis hash will not match chain.rlp.
    header.base_fee_per_gas = 0x3b9aca00;
    header.withdrawals_root = NULL_ROOT;
    return {header, HIVE_NET_ALLOC};
}

MONAD_NAMESPACE_END
