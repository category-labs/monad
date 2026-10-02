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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/hive_net.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/chain/chain_factory.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/switch_traits.hpp>

#include <cstdint>
#include <memory>

MONAD_NAMESPACE_BEGIN

std::unique_ptr<Chain> make_chain(monad_chain_config const chain_config)
{
    switch (chain_config) {
    case CHAIN_CONFIG_ETHEREUM_MAINNET:
        return std::make_unique<EthereumMainnet>();
    case CHAIN_CONFIG_MONAD_DEVNET:
        return std::make_unique<MonadDevnet>();
    case CHAIN_CONFIG_MONAD_TESTNET:
        return std::make_unique<MonadTestnet>();
    case CHAIN_CONFIG_MONAD_MAINNET:
        return std::make_unique<MonadMainnet>();
    case CHAIN_CONFIG_HIVE_NET:
        return std::make_unique<HiveNet>();
    }
    MONAD_ASSERT(false);
}

std::unique_ptr<MonadChain>
make_monad_chain(monad_chain_config const chain_config)
{
    switch (chain_config) {
    case CHAIN_CONFIG_MONAD_DEVNET:
        return std::make_unique<MonadDevnet>();
    case CHAIN_CONFIG_MONAD_TESTNET:
        return std::make_unique<MonadTestnet>();
    case CHAIN_CONFIG_MONAD_MAINNET:
        return std::make_unique<MonadMainnet>();
    case CHAIN_CONFIG_ETHEREUM_MAINNET:
    case CHAIN_CONFIG_HIVE_NET:
        MONAD_ABORT_PRINTF(
            "expected a Monad chain config, got %d", chain_config);
    }
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END

MONAD_ANONYMOUS_NAMESPACE_BEGIN

monad_eth_header_layout evm_header_layout(
    Chain const &chain, uint64_t const block_number, uint64_t const timestamp)
{
    monad_eth_revision const rev = chain.get_revision(block_number, timestamp);
    SWITCH_EVM_TRAITS(eth_header_layout);
    return MONAD_ETH_HEADER_LAYOUT_UNKNOWN;
}

monad_eth_header_layout
monad_header_layout(MonadChain const &chain, uint64_t const timestamp)
{
    monad_revision const rev = chain.get_monad_revision(timestamp);
    SWITCH_MONAD_TRAITS(eth_header_layout);
    return MONAD_ETH_HEADER_LAYOUT_UNKNOWN;
}

MONAD_ANONYMOUS_NAMESPACE_END

enum monad_eth_header_layout monad_chain_eth_header_layout(
    enum monad_chain_config const chain_config, uint64_t const block_number,
    uint64_t const timestamp)
{
    using namespace monad;

    switch (chain_config) {
    case CHAIN_CONFIG_ETHEREUM_MAINNET:
        if (MONAD_UNLIKELY(
                block_number <
                constants::EARLIEST_SUPPORTED_ETH_BLOCK_NUMBER)) {
            return MONAD_ETH_HEADER_LAYOUT_UNKNOWN;
        }
        return evm_header_layout(EthereumMainnet{}, block_number, timestamp);
    case CHAIN_CONFIG_HIVE_NET:
        return evm_header_layout(HiveNet{}, block_number, timestamp);
    case CHAIN_CONFIG_MONAD_DEVNET:
        return monad_header_layout(MonadDevnet{}, timestamp);
    case CHAIN_CONFIG_MONAD_TESTNET:
        return monad_header_layout(MonadTestnet{}, timestamp);
    case CHAIN_CONFIG_MONAD_MAINNET:
        return monad_header_layout(MonadMainnet{}, timestamp);
    }
    return MONAD_ETH_HEADER_LAYOUT_UNKNOWN;
}
