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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class DomainBlockStore;
class L1Source;
class PrivateDomainKeyring;

// Derives one private domain's blocks from the finalized L1 chain into its
// store, one L1 block at a time, in order.
class PrivateDomainDeriver
{
    L1Source const &l1_;
    DomainBlockStore &store_;
    PrivateDomainKeyring const &keyring_;
    Address hub_;
    uint64_t next_l1_block_;

public:
    // `keyring` holds the one domain to derive. The deriver continues after
    // the store's cursor, or after its tip's L1 block if a crash left that
    // later, and starts from `start_l1_block` on an empty store.
    PrivateDomainDeriver(
        L1Source const &, DomainBlockStore &,
        PrivateDomainKeyring const &keyring, Address const &hub,
        uint64_t start_l1_block);

    uint64_t next_l1_block() const
    {
        return next_l1_block_;
    }

    // Derives the next L1 block if it is finalized, and returns whether it
    // did. Fails, deriving nothing, if the block has left the L1 source's
    // history or holds a malformed hub event of the domain.
    Result<bool> derive_next();
};

MONAD_NAMESPACE_END
