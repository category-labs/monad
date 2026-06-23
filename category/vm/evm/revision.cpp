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

#include <category/core/assert.h>
#include <category/vm/evm/revision.h>

#include <evmc/evmc.h>

#include <utility>

// Enforce the 1:1 correspondence with evmc_revision that makes the conversions
// below value-preserving casts. If evmc ever renumbers a revision, these fire.
#define MONAD_ASSERT_REVISION_EQ(rev)                                          \
    static_assert(                                                             \
        std::to_underlying(MONAD_ETH_##rev) == std::to_underlying(EVMC_##rev))

MONAD_ASSERT_REVISION_EQ(FRONTIER);
MONAD_ASSERT_REVISION_EQ(HOMESTEAD);
MONAD_ASSERT_REVISION_EQ(TANGERINE_WHISTLE);
MONAD_ASSERT_REVISION_EQ(SPURIOUS_DRAGON);
MONAD_ASSERT_REVISION_EQ(BYZANTIUM);
MONAD_ASSERT_REVISION_EQ(CONSTANTINOPLE);
MONAD_ASSERT_REVISION_EQ(PETERSBURG);
MONAD_ASSERT_REVISION_EQ(ISTANBUL);
MONAD_ASSERT_REVISION_EQ(BERLIN);
MONAD_ASSERT_REVISION_EQ(LONDON);
MONAD_ASSERT_REVISION_EQ(PARIS);
MONAD_ASSERT_REVISION_EQ(SHANGHAI);
MONAD_ASSERT_REVISION_EQ(CANCUN);
MONAD_ASSERT_REVISION_EQ(PRAGUE);
MONAD_ASSERT_REVISION_EQ(OSAKA);

#undef MONAD_ASSERT_REVISION_EQ

// MONAD_ETH_AMSTERDAM and the MONAD_ETH_EXPERIMENTAL / MONAD_ETH_MAX_REVISION
// sentinel above it have no evmc_revision counterpart in the bundled evmc
// (whose enum stops at EVMC_OSAKA followed by EVMC_EXPERIMENTAL == 15), so they
// are not asserted equal above. The per-revision asserts through OSAKA keep the
// bare casts below value-preserving across the evmc-backed range
// (FRONTIER..OSAKA).
//
// MONAD_ETH_LATEST_STABLE_REVISION likewise intentionally diverges from
// EVMC_LATEST_STABLE_REVISION (still Cancun in the bundled evmc).

// Map a monad_eth_revision to evmc_revision at the remaining evmc/evmone
// boundaries (test and benchmark paths). Only FRONTIER..OSAKA are convertible;
// they mirror evmc_revision 1:1 (asserted above).
//
// AMSTERDAM (and the EXPERIMENTAL sentinel above it) have no evmc counterpart.
// Amsterdam support is in progress and its behavior will diverge from OSAKA, so
// it must NOT be silently substituted with another revision here: handing
// evmone OSAKA — or, via a bare cast, EVMC_EXPERIMENTAL — would compare Monad's
// Amsterdam against the wrong reference semantics. Abort instead until evmc
// gains a real Amsterdam value.
// TODO(amsterdam): convert AMSTERDAM to its evmc revision once one exists.
evmc_revision to_evmc_revision(monad_eth_revision const rev)
{
    MONAD_ASSERT(rev <= MONAD_ETH_OSAKA);
    return static_cast<evmc_revision>(std::to_underlying(rev));
}

// The inverse only ever receives real evmc revisions. EVMC_EXPERIMENTAL — which
// a bare cast would turn into AMSTERDAM, since they share the value 15 — is a
// sentinel and is rejected rather than silently misinterpreted.
monad_eth_revision from_evmc_revision(evmc_revision const rev)
{
    MONAD_ASSERT(rev <= EVMC_OSAKA);
    return static_cast<monad_eth_revision>(std::to_underlying(rev));
}

char const *monad_eth_revision_to_string(monad_eth_revision const rev)
{
    switch (rev) {
    case MONAD_ETH_FRONTIER:
        return "MONAD_ETH_FRONTIER";
    case MONAD_ETH_HOMESTEAD:
        return "MONAD_ETH_HOMESTEAD";
    case MONAD_ETH_TANGERINE_WHISTLE:
        return "MONAD_ETH_TANGERINE_WHISTLE";
    case MONAD_ETH_SPURIOUS_DRAGON:
        return "MONAD_ETH_SPURIOUS_DRAGON";
    case MONAD_ETH_BYZANTIUM:
        return "MONAD_ETH_BYZANTIUM";
    case MONAD_ETH_CONSTANTINOPLE:
        return "MONAD_ETH_CONSTANTINOPLE";
    case MONAD_ETH_PETERSBURG:
        return "MONAD_ETH_PETERSBURG";
    case MONAD_ETH_ISTANBUL:
        return "MONAD_ETH_ISTANBUL";
    case MONAD_ETH_BERLIN:
        return "MONAD_ETH_BERLIN";
    case MONAD_ETH_LONDON:
        return "MONAD_ETH_LONDON";
    case MONAD_ETH_PARIS:
        return "MONAD_ETH_PARIS";
    case MONAD_ETH_SHANGHAI:
        return "MONAD_ETH_SHANGHAI";
    case MONAD_ETH_CANCUN:
        return "MONAD_ETH_CANCUN";
    case MONAD_ETH_PRAGUE:
        return "MONAD_ETH_PRAGUE";
    case MONAD_ETH_OSAKA:
        return "MONAD_ETH_OSAKA";
    case MONAD_ETH_AMSTERDAM:
        return "MONAD_ETH_AMSTERDAM";
    case MONAD_ETH_EXPERIMENTAL:
        return "MONAD_ETH_EXPERIMENTAL";
    }
    MONAD_ABORT("unhandled monad_eth_revision");
}
