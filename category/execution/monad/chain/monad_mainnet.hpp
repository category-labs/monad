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

MONAD_NAMESPACE_BEGIN

struct MonadMainnet : MonadChain
{
    virtual monad_revision
    get_monad_revision(uint64_t timestamp) const override;

    virtual uint256_t get_chain_id() const override;

    virtual GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
