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

#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

// EVM fork revisions, ordered so that later forks compare greater.
enum monad_eth_revision
{
    MONAD_ETH_FRONTIER = 0,
    MONAD_ETH_HOMESTEAD = 1,
    MONAD_ETH_TANGERINE_WHISTLE = 2,
    MONAD_ETH_SPURIOUS_DRAGON = 3,
    MONAD_ETH_BYZANTIUM = 4,
    MONAD_ETH_CONSTANTINOPLE = 5,
    MONAD_ETH_PETERSBURG = 6,
    MONAD_ETH_ISTANBUL = 7,
    MONAD_ETH_BERLIN = 8,
    MONAD_ETH_LONDON = 9,
    MONAD_ETH_PARIS = 10,
    MONAD_ETH_SHANGHAI = 11,
    MONAD_ETH_CANCUN = 12,
    MONAD_ETH_PRAGUE = 13,
    MONAD_ETH_OSAKA = 14,
    MONAD_ETH_AMSTERDAM = 15,
    MONAD_ETH_EXPERIMENTAL = 16,

    // The maximum EVM revision supported.
    MONAD_ETH_MAX_REVISION = MONAD_ETH_EXPERIMENTAL,

    // The latest known EVM revision with finalized specification.
    MONAD_ETH_LATEST_STABLE_REVISION = MONAD_ETH_PRAGUE
};

char const *monad_eth_revision_to_string(enum monad_eth_revision rev);

#ifdef __cplusplus
} // extern "C"
#endif
