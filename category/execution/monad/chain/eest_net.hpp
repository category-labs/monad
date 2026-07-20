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

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/vm/evm/monad/revision.h>

#include <string>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

inline constexpr uint64_t EEST_NET_CHAIN_ID = 30143;

// Revision activations by block timestamp, ascending; the first entry
// must activate at timestamp 0.
using EestNetRevisionSchedule =
    std::vector<std::pair<uint64_t, monad_revision>>;

// Chain for executing EEST (execution-spec-tests) blockchain fixtures
// against the production runloop. The genesis allocation (the fixture's
// `pre` state), the genesis block header (the fixture's genesis, so
// that the parent hash of block 1 matches the fixture's) and the
// revision schedule (derived from the fixture's `network`; a single
// entry for non-transition fixtures) are supplied at runtime instead
// of being compiled in.
struct EestNet : MonadChain
{
    EestNet(
        std::string genesis_alloc, BlockHeader genesis_header,
        EestNetRevisionSchedule schedule);

    virtual monad_revision
    get_monad_revision(uint64_t timestamp) const override;

    virtual uint256_t get_chain_id() const override;

    virtual GenesisState get_genesis_state() const override;

private:
    std::string genesis_alloc_;
    BlockHeader genesis_header_;
    EestNetRevisionSchedule schedule_;
};

MONAD_NAMESPACE_END
