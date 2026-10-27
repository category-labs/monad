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

#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

// Header of a private domain block as derived from one L1 block, before
// execution. Every field is determined by the L1 block and the domain's
// previous header alone. Like an Ethereum header, it has no chain id: a
// domain's comes from its configuration. See PROTOCOL.md in
// category-labs/monad-domains.
struct DomainBlockHeader
{
    // domain_block_id of the previous domain block; zero for genesis.
    bytes32_t parent_id{};
    // Domain block height: 0 is genesis, then +1 per derived block. Not the
    // L1 block number.
    uint64_t number{};
    uint64_t l1_block_number{};
    // The L1 block's Ethereum block hash, keccak256(rlp(header)).
    bytes32_t l1_block_hash{};
    // Copied from the L1 block.
    uint64_t timestamp{};
    bytes32_t mix_hash{};
    // Protocol constants: the most gas the hub sells per domain per L1 block,
    // and the price it sells it at.
    uint64_t gas_limit{};
    uint256_t base_fee_per_gas{};
    // Ordered trie root of the block's transactions.
    bytes32_t transactions_root{NULL_ROOT};
    // Copied from the L1 block (EIP-7843): present iff its header has it.
    std::optional<uint64_t> slot_number{};

    friend bool
    operator==(DomainBlockHeader const &, DomainBlockHeader const &) = default;
};

// A derived domain block. The sequence of DomainBlocks from genesis is the
// domain's canonical history: executing them in order rebuilds its state.
struct DomainBlock
{
    DomainBlockHeader header;
    std::vector<Transaction> transactions;

    friend bool operator==(DomainBlock const &, DomainBlock const &) = default;
};

// The id a domain block is known by before it executes, as an L1 block is by
// its consensus id: keccak256(rlp(header)) of its DomainBlockHeader. The
// next block names it in parent_id, and execution commits the block under it.
bytes32_t domain_block_id(DomainBlockHeader const &);

MONAD_DOMAIN_NAMESPACE_END
