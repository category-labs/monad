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
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Header of a private domain block as derived from one L1 block, before
// execution. Every field is determined by the L1 block and the domain's
// previous header alone. See docs/domains-protocol.md.
struct ProposedDomainHeader
{
    uint64_t domain_chain_id{};
    // Domain block height: 0 is genesis, then +1 per derived block. Not the
    // L1 block number.
    uint64_t number{};
    uint64_t l1_block_number{};
    bytes32_t l1_block_id{};
    // Copied from the L1 block.
    uint64_t timestamp{};
    bytes32_t mix_hash{};
    // Protocol constants: the most gas the hub sells per domain per L1 block,
    // and the price it sells it at.
    uint64_t gas_limit{};
    uint256_t base_fee_per_gas{};
    // Ordered trie root of the block's transactions.
    bytes32_t transactions_root{NULL_ROOT};

    friend bool operator==(
        ProposedDomainHeader const &, ProposedDomainHeader const &) = default;
};

// A derived domain block. The sequence of DomainBlocks from genesis is the
// domain's canonical history: executing them in order rebuilds its state.
// Ommers and withdrawals are always empty and exist only in the encoding.
struct DomainBlock
{
    ProposedDomainHeader header;
    std::vector<Transaction> transactions;

    friend bool operator==(DomainBlock const &, DomainBlock const &) = default;
};

MONAD_NAMESPACE_END
