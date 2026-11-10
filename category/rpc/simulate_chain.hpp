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

#include <category/core/config.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/vm/evm/revision.h>

#include <cstdint>
#include <memory>

MONAD_NAMESPACE_BEGIN

// Ethereum-family chain that executes every block under a fixed fork instead
// of deriving the fork from the block number and timestamp, e.g. to run
// ethereum-tests fixtures whose environment predates the fork on mainnet. The
// chain id and genesis state come from the wrapped chain; the blob schedule is
// the pinned fork's default, so blob-parameter-only forks (BPOs) are not
// modeled.
class SimulateEvmChain final : public Chain
{
    std::unique_ptr<Chain const> inner_;
    monad_eth_revision rev_;
    BlobSchedule blob_schedule_;

public:
    // Whether `rev` is a fork that can be pinned.
    static bool is_supported_revision(monad_eth_revision rev);

    // Requires `inner` to be a non-null, non-Monad chain and `rev` to satisfy
    // `is_supported_revision`.
    SimulateEvmChain(
        std::unique_ptr<Chain const> inner, monad_eth_revision rev);

    uint256_t get_chain_id() const override;

    monad_eth_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    BlobSchedule get_blob_schedule(uint64_t timestamp) const override;

    GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
