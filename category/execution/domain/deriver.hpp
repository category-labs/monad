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
#include <category/execution/domain/derivation.hpp>

#include <cstdint>
#include <functional>
#include <optional>

MONAD_DOMAIN_NAMESPACE_BEGIN

class L1Source;
class PrivateDomainKey;

// Where derivation of a domain is: the next L1 block to derive, and the
// number the domain's next block gets, none before genesis. It is not saved:
// a restart finds it again with find_derivation_start.
struct DerivationCursor
{
    uint64_t next_l1_block{};
    std::optional<uint64_t> next_block{};

    friend bool
    operator==(DerivationCursor const &, DerivationCursor const &) = default;
};

// The hub's storage slot that holds a domain's latest block:
// blockNumber(64) | domainBlockNumber(64) | gasSold(128), where blockNumber
// is the L1 block the domain block is derived from. Zero until the domain is
// registered. Mirrors DomainHub's budget word, the third slot of the domain's
// input queue.
bytes32_t latest_domain_block_slot(uint64_t domain_chain_id);

// Where derivation continues for a domain whose blocks up to `executed` have
// been executed, none if it has no blocks, from the hub's state on L1 alone.
// The domain's next block is derived from the first L1 block at which the
// hub's latest block of the domain is past `executed`. If there is none yet,
// derivation continues after the latest finalized L1 block.
//
// Fails with mpt::DbError::version_no_longer_exist if that L1 block has left
// the source's history, and with DomainDerivationError::AheadOfHub if the hub
// has not recorded block `executed`.
Result<DerivationCursor> find_derivation_start(
    L1Source const &, Address const &hub, uint64_t domain_chain_id,
    std::optional<uint64_t> executed);

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

    // Derives the next L1 block if it is finalized, hands its domain block,
    // if there is one, to `on_block` and moves on; returns whether it
    // derived. Fails, moving nothing, if the block has left the L1 source's
    // history, holds a malformed hub event of the domain, holds inputs of the
    // domain before its registration was derived, or `on_block` fails.
    Result<bool> derive_next(BlockHandler const &on_block);
};

MONAD_DOMAIN_NAMESPACE_END
