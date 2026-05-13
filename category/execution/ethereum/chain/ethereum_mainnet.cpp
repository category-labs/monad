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

#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>

#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/chain/ethereum_mainnet_alloc.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/validate_block.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

uint256_t EthereumMainnet::get_chain_id() const
{
    return 1;
};

BlobSchedule EthereumMainnet::get_blob_schedule(
    uint64_t const /*block_number*/, uint64_t const timestamp) const
{
    // BPO2 (EIP-7892): target=14, max=21, fraction=11684671
    //   1767747671 = 2026-01-07 UTC
    if (timestamp >= 1767747671) {
        return {14, 21, 11'684'671};
    }
    // BPO1 (EIP-7892): target=10, max=15, fraction=8346193
    //   1765290071 = 2025-12-09 UTC
    if (timestamp >= 1765290071) {
        return {10, 15, 8'346'193};
    }
    // Osaka (Fusaka): target=6, max=9, fraction=5007716
    //   1764798551 = 2025-12-03 UTC (block 23935694)
    if (timestamp >= 1764798551) {
        return {6, 9, 5'007'716};
    }
    // Prague (EIP-7691): target=6, max=9, fraction=5007716
    //   1746612311 = 2025-05-07 UTC (block 22431084)
    if (timestamp >= 1746612311) {
        return {6, 9, 5'007'716};
    }
    // Cancun (EIP-4844): target=3, max=6, fraction=3338477
    //   1710338135 = 2024-03-13 UTC (block 19426587)
    if (timestamp >= 1710338135) {
        return {3, 6, 3'338'477};
    }
    return {0, 0, 1};
}

monad_eth_revision EthereumMainnet::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    // Osaka (Fusaka) activation timestamp on mainnet:
    //   1764798551 = 2025-12-03 21:49:11 UTC (block 23935694)
    if (timestamp >= 1764798551) {
        return MONAD_ETH_OSAKA;
    }
    // Prague (Pectra) activation timestamp on mainnet:
    //   1746612311 = 2025-05-07 10:05:11 UTC (block 22431084)
    else if (MONAD_LIKELY(timestamp >= 1746612311)) {
        return MONAD_ETH_PRAGUE;
    }
    else if (timestamp >= 1710338135) {
        return MONAD_ETH_CANCUN;
    }
    else if (timestamp >= 1681338455) {
        return MONAD_ETH_SHANGHAI;
    }
    else if (block_number >= 15537394) {
        return MONAD_ETH_PARIS;
    }
    else if (block_number >= 12965000) {
        return MONAD_ETH_LONDON;
    }
    else if (block_number >= 12244000) {
        return MONAD_ETH_BERLIN;
    }
    else if (block_number >= 9069000) {
        return MONAD_ETH_ISTANBUL;
    }
    else if (block_number >= 7280000) {
        return MONAD_ETH_PETERSBURG;
    }
    MONAD_ASSERT(false, "unsupported fork");
}

GenesisState EthereumMainnet::get_genesis_state() const
{
    BlockHeader header;
    header.difficulty = 17179869184;
    header.gas_limit = 5000;
    store_be(header.nonce.data(), uint64_t{66});
    header.extra_data = from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                                 "db3db69cbdb7a38e1e50b1b82fa")
                            .value();
    return {header, ETHEREUM_MAINNET_ALLOC};
}

MONAD_NAMESPACE_END
