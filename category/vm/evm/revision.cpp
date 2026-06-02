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
MONAD_ASSERT_REVISION_EQ(EXPERIMENTAL);
MONAD_ASSERT_REVISION_EQ(MAX_REVISION);

#undef MONAD_ASSERT_REVISION_EQ

// MONAD_ETH_LATEST_STABLE_REVISION intentionally diverges from
// EVMC_LATEST_STABLE_REVISION (still Cancun in the bundled evmc), so it is not
// asserted equal above. The per-revision asserts already guarantee the
// conversions below are value-preserving.

// These are value-preserving casts: monad_eth_revision mirrors evmc_revision
// 1:1, enforced by the static_asserts above. C linkage matches the declarations
// in revision.h.
evmc_revision to_evmc_revision(monad_eth_revision const rev)
{
    return static_cast<evmc_revision>(std::to_underlying(rev));
}

monad_eth_revision from_evmc_revision(evmc_revision const rev)
{
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
    case MONAD_ETH_EXPERIMENTAL:
        return "MONAD_ETH_EXPERIMENTAL";
    }
    MONAD_ABORT("unhandled monad_eth_revision");
}
