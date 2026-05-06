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
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/hive_net.hpp>
#include <category/execution/monad/chain/chain_factory.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>

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
