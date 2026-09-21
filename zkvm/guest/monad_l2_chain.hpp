// Copyright (C) 2026 Category Labs, Inc.
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

// The L2 prototype's chain. It lives under zkvm/ and not in
// category/execution/ethereum/chain/ so the host tree does not build a chain
// nobody instantiates.
//
// Two differences from EthereumMainnet, both deliberate: a chain id of its own,
// and a revision that is a constant rather than a lookup on a fork schedule.

#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/vm/evm/revision.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct MonadL2 : Chain
{
    virtual uint256_t get_chain_id() const override;

    virtual monad_eth_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual BlobSchedule get_blob_schedule(uint64_t timestamp) const override;

    virtual GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
