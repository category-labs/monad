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

#include <evmc/evmc.h>

#ifdef __cplusplus
extern "C"
{
#endif

// Monad's in-tree EVM fork revision enum. This is a drop-in replacement for
// evmc's `evmc_revision`: the enumerators mirror `evmc_revision` 1:1 (same
// underlying integer values), which keeps ordering comparisons, the arithmetic
// in previous_evm_revision(), and Traits::id() numerically unchanged. The
// 1:1 correspondence is enforced by static_assert in revision.cpp.
//
// The enum itself carries no evmc dependency. The only tie to evmc is the pair
// of conversion functions below, which are needed solely at the remaining
// evmc/evmone boundaries (test and benchmark paths); they — together with the
// <evmc/evmc.h> include — are removable in one step once evmone is gone, after
// which these enumerators can diverge from evmc and grow future forks freely.
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
    MONAD_ETH_EXPERIMENTAL = 15,

    // The maximum EVM revision supported.
    MONAD_ETH_MAX_REVISION = MONAD_ETH_EXPERIMENTAL,

    // The latest known EVM revision with finalized specification.
    MONAD_ETH_LATEST_STABLE_REVISION = MONAD_ETH_CANCUN
};

char const *monad_eth_revision_to_string(enum monad_eth_revision rev);

// Convert between monad_eth_revision and evmc's evmc_revision. Needed only at
// the remaining evmc/evmone boundaries (see the note above).
enum evmc_revision to_evmc_revision(enum monad_eth_revision rev);
enum monad_eth_revision from_evmc_revision(enum evmc_revision rev);

#ifdef __cplusplus
} // extern "C"
#endif
