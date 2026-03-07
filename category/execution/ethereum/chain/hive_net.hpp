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

#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>

MONAD_NAMESPACE_BEGIN

struct HiveNet : EthereumMainnet
{
    virtual uint256_t get_chain_id() const override;

    virtual bool should_process_eip_requests() const override
    {
        return true;
    }

    virtual evmc_revision
    get_revision(uint64_t block_number, uint64_t timestamp) const override;

    virtual GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
