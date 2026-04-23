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
#include <category/execution/ethereum/chain/hive_net.hpp>
#include <category/execution/ethereum/chain/hive_net_alloc.hpp>

MONAD_NAMESPACE_BEGIN

uint256_t HiveNet::get_chain_id() const
{
    return 3503995874084926;
}

// Fork schedule from the hive tests:
// see: https://github.com/ethereum/execution-apis/blob/main/tests/genesis.json
// see: https://github.com/ethereum/execution-apis/blob/main/tests/forkenv.json
evmc_revision HiveNet::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    if (block_number >= 36) {
        if (timestamp >= 450) {
            return EVMC_PRAGUE;
        }
        if (timestamp >= 420) {
            return EVMC_CANCUN;
        }
        if (timestamp >= 390) {
            return EVMC_SHANGHAI;
        }
        return EVMC_PARIS;
    }
    if (block_number >= 27) {
        return EVMC_LONDON;
    }
    if (block_number >= 24) {
        return EVMC_BERLIN;
    }
    if (block_number >= 18) {
        return EVMC_ISTANBUL;
    }
    if (block_number >= 12) {
        return EVMC_PETERSBURG;
    }
    if (block_number >= 9) {
        return EVMC_BYZANTIUM;
    }
    if (block_number >= 6) {
        return EVMC_SPURIOUS_DRAGON;
    }
    if (block_number >= 3) {
        return EVMC_TANGERINE_WHISTLE;
    }
    return EVMC_HOMESTEAD;
}

GenesisState HiveNet::get_genesis_state() const
{
    BlockHeader header;
    header.difficulty = 0x20000;
    header.gas_limit = 0x23f3e20;
    intx::be::unsafe::store<uint64_t>(header.nonce.data(), 0x0);
    header.extra_data = from_hex("0x68697665636861696e").value();
    return {header, HIVE_NET_ALLOC};
}

MONAD_NAMESPACE_END
