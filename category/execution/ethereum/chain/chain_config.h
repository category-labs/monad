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

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_chain_config
{
    CHAIN_CONFIG_ETHEREUM_MAINNET = 0,
    CHAIN_CONFIG_MONAD_DEVNET = 1,
    CHAIN_CONFIG_MONAD_TESTNET = 2,
    CHAIN_CONFIG_MONAD_MAINNET = 3,
    CHAIN_CONFIG_HIVE_NET = 4,
};

// Optional header fields a block carries; each layout adds to the previous.
enum monad_eth_header_layout
{
    MONAD_ETH_HEADER_LAYOUT_UNKNOWN = 0, // Not determinable
    MONAD_ETH_HEADER_LAYOUT_LEGACY = 1, // No optional fields
    MONAD_ETH_HEADER_LAYOUT_LONDON = 2, // + base_fee_per_gas (EIP-1559)
    MONAD_ETH_HEADER_LAYOUT_SHANGHAI = 3, // + withdrawals_root (EIP-4895)
    MONAD_ETH_HEADER_LAYOUT_CANCUN = 4, // + blob_gas_used, excess_blob_gas
                                        // (EIP-4844), parent_beacon_block_root
                                        // (EIP-4788)
    MONAD_ETH_HEADER_LAYOUT_PRAGUE = 5, // + requests_hash (EIP-7685)
    MONAD_ETH_HEADER_LAYOUT_AMSTERDAM = 6, // + block_access_list_hash
                                           // (EIP-7928), slot_number (EIP-7843)
};

// Header layout of an executed (non-genesis) block; UNKNOWN for an
// unrecognised chain or an Ethereum mainnet block before the earliest
// supported fork.
enum monad_eth_header_layout monad_chain_eth_header_layout(
    enum monad_chain_config chain_config, uint64_t block_number,
    uint64_t timestamp);

#ifdef __cplusplus
}
#endif
