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

// Guest L2 chain with its own chain id and a fixed revision. Kept under zkvm
// because ordinary host execution does not instantiate it.

#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/revision.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

/// A MonadChain, not a Chain: the client refuses gasless execution on EvmTraits
/// at compile time -- its path carries
/// static_assert(!gasless || is_monad_trait_v<traits>) -- so a domain that
/// meters gas without pricing it has no other family available. Monad pricing,
/// the reserve balance, cold-access costs and the code-size limits follow, and
/// all of them move the state root.
struct MonadL2 : MonadChain
{
    virtual uint256_t get_chain_id() const override;

    virtual monad_revision get_monad_revision(uint64_t timestamp) const override;

    virtual BlobSchedule get_blob_schedule(uint64_t timestamp) const override;

    virtual GenesisState get_genesis_state() const override;
};

MONAD_NAMESPACE_END
