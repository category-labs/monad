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

#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/monad/chain/monad_devnet_alloc.hpp>
#include <category/execution/monad/chain/monad_devnet_fork.hpp>
#include <category/vm/evm/monad/revision.h>
#include <cstdint>
#include <cstdlib>
#include <limits>

MONAD_NAMESPACE_BEGIN

monad_revision
MonadDevnetFork::get_monad_revision(uint64_t const timestamp) const
{
    // Cached on first call: the fork timestamp is read from
    // MONAD_DEVNETFORK_NEXT_AT (UNIX seconds). Unset -> sentinel that
    // never compares <= any real timestamp, so the chain stays MONAD_NINE.
    // The test harness sets this before launching node containers so the
    // fork lands a configurable wall-clock interval after genesis.
    static auto const next_at = []() -> uint64_t {
        char const *const env = std::getenv("MONAD_DEVNETFORK_NEXT_AT");
        if (env == nullptr || *env == '\0') {
            return std::numeric_limits<uint64_t>::max();
        }
        return std::strtoull(env, nullptr, 10);
    }();
    return timestamp >= next_at ? MONAD_NEXT : MONAD_NINE;
}

uint256_t MonadDevnetFork::get_chain_id() const
{
    // Devnet (20143) + 1. Distinct so a test cluster can't accidentally
    // mix with a regular devnet pool.
    return 20144;
}

GenesisState MonadDevnetFork::get_genesis_state() const
{
    BlockHeader header;
    header.difficulty = 17179869184;
    header.gas_limit = 5000;
    store_be(header.nonce.data(), uint64_t{66});
    header.extra_data = from_hex("0x11bbe8db4e347b4e8c937c1c8370e4b5ed33a"
                                 "db3db69cbdb7a38e1e50b1b82fa")
                            .value();
    return {header, MONAD_DEVNET_ALLOC};
}

MONAD_NAMESPACE_END
