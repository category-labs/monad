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

using BOOST_OUTCOME_V2_NAMESPACE::success;

MONAD_NAMESPACE_BEGIN

using namespace eth_forks;

uint256_t EthereumMainnet::get_chain_id() const
{
    return 1;
};

monad_eth_revision EthereumMainnet::get_revision(
    uint64_t const block_number, uint64_t const timestamp) const
{
    if (MONAD_LIKELY(timestamp >= PRAGUE_ACTIVATION_TIMESTAMP)) {
        return MONAD_ETH_PRAGUE;
    }
    else if (timestamp >= CANCUN_ACTIVATION_TIMESTAMP) {
        return MONAD_ETH_CANCUN;
    }
    else if (timestamp >= SHANGHAI_ACTIVATION_TIMESTAMP) {
        return MONAD_ETH_SHANGHAI;
    }
    else if (block_number >= PARIS_ACTIVATION_BLOCK_NUMBER) {
        return MONAD_ETH_PARIS;
    }
    else if (block_number >= LONDON_ACTIVATION_BLOCK_NUMBER) {
        return MONAD_ETH_LONDON;
    }
    else if (block_number >= BERLIN_ACTIVATION_BLOCK_NUMBER) {
        return MONAD_ETH_BERLIN;
    }
    else if (block_number >= ISTANBUL_ACTIVATION_BLOCK_NUMBER) {
        return MONAD_ETH_ISTANBUL;
    }
    MONAD_ASSERT(false, "unsupported fork");
}

BlobSchedule EthereumMainnet::get_blob_schedule(uint64_t const timestamp) const
{
    if (timestamp >= BPO1_ACTIVATION_TIMESTAMP &&
        get_revision(0, timestamp) >= MONAD_ETH_OSAKA) {
        if (MONAD_LIKELY(timestamp >= BPO2_ACTIVATION_TIMESTAMP)) {
            return BPO2_BLOB_SCHEDULE;
        }
        return BPO1_BLOB_SCHEDULE;
    }
    if (timestamp >= PRAGUE_ACTIVATION_TIMESTAMP) {
        return PRAGUE_BLOB_SCHEDULE;
    }
    return CANCUN_BLOB_SCHEDULE;
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
