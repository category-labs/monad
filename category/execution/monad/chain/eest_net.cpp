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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/monad/chain/eest_net.hpp>
#include <category/vm/evm/monad/revision.h>

#include <utility>

MONAD_NAMESPACE_BEGIN

EestNet::EestNet(
    std::string genesis_alloc, BlockHeader genesis_header,
    EestNetRevisionSchedule schedule)
    : genesis_alloc_{std::move(genesis_alloc)}
    , genesis_header_{std::move(genesis_header)}
    , schedule_{std::move(schedule)}
{
    MONAD_ASSERT(!schedule_.empty());
    MONAD_ASSERT(schedule_.front().first == 0);
}

monad_revision EestNet::get_monad_revision(uint64_t const timestamp) const
{
    monad_revision revision = schedule_.front().second;
    for (auto const &[from_timestamp, rev] : schedule_) {
        if (timestamp >= from_timestamp) {
            revision = rev;
        }
    }
    return revision;
}

uint256_t EestNet::get_chain_id() const
{
    return EEST_NET_CHAIN_ID;
}

GenesisState EestNet::get_genesis_state() const
{
    return {genesis_header_, genesis_alloc_.c_str()};
}

MONAD_NAMESPACE_END
