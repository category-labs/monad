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
    CHAIN_CONFIG_MONAD_TESTNET2 = 4,
};

#ifdef __cplusplus
}
#endif
