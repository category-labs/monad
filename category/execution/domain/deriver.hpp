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
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/domain_block.hpp>

#include <cstdint>
#include <functional>

MONAD_DOMAIN_NAMESPACE_BEGIN

class L1Source;
class PrivateDomainKey;

// Where derivation of a domain is: the next L1 block to derive, and the
// number the domain's next block gets, 0 before genesis. It is not saved:
// a restart finds it again with find_derivation_start.
struct DerivationCursor
{
    uint64_t next_l1_block{};
    uint64_t next_block{};

    friend bool
    operator==(DerivationCursor const &, DerivationCursor const &) = default;
};

// The hub storage slot that holds a domain's latest block word: gasSold(128) |
// l1BlockNumber(64) | domainBlockNumber(64). Zero until the domain is
// registered.
bytes32_t latest_domain_block_slot(uint64_t domain_chain_id);

// Finds where derivation resumes for a domain whose next block is `target`: the
// first L1 block at which the hub has recorded block `target`, or the block
// after the latest finalized one if it has not yet.
//
// Fails with mpt::DbError::version_no_longer_exist if that L1 block has left
// the source's history, and with DomainDerivationError::AheadOfHub if the hub
// has not recorded the block before `target`.
Result<DerivationCursor> find_derivation_start(
    L1Source const &, Address const &hub, uint64_t domain_chain_id,
    uint64_t target);

// Derives one private domain's blocks from the finalized L1 chain, one L1
// block at a time, in order, and hands each block on.
class PrivateDomainDeriver
{
public:
    // Takes a derived block. A failure stops derivation before the cursor
    // moves past the block's L1 block.
    using BlockHandler =
        std::function<Result<void>(DerivedDomainBlock const &)>;

private:
    L1Source const &l1_;
    PrivateDomainKey const &key_;
    DomainConfig domain_;
    Address hub_;
    DerivationCursor cursor_;

public:
    // Derives the domain `domain_chain_id`, whose transactions are sealed to
    // `key` and whose deliveries go to `spoke`, from `cursor` on.
    PrivateDomainDeriver(
        L1Source const &, PrivateDomainKey const &key, uint64_t domain_chain_id,
        Address const &spoke, Address const &hub, DerivationCursor cursor);

    DerivationCursor const &cursor() const
    {
        return cursor_;
    }

    // Derives the next L1 block if it is finalized and passes its domain block,
    // if any, to `on_block`. Returns whether it derived. On failure the cursor
    // does not move.
    Result<bool> derive_next(BlockHandler const &on_block);
};

MONAD_DOMAIN_NAMESPACE_END
