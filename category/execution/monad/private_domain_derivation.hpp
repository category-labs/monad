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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/monad/core/domain_block.hpp>

#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

// Price of one unit of domain gas in L1 wei, and the most gas the hub sells
// per domain per L1 block. Mirror DomainHub.DOMAIN_GAS_PRICE and
// DomainHub.DOMAIN_BLOCK_GAS_LIMIT. Every domain block has this gas limit and
// this base fee.
inline constexpr uint256_t DOMAIN_GAS_PRICE{50'000'000'000};
inline constexpr uint64_t DOMAIN_BLOCK_GAS_LIMIT = 150'000'000;

// Domain gas a fee paid to the hub buys.
uint64_t purchased_domain_gas(uint256_t const &fee);

// The L1 block domain blocks are derived from, after L1 execution.
struct DomainDerivationInput
{
    BlockHeader const &l1_header;
    bytes32_t l1_block_id;
    std::span<Receipt const> l1_receipts;
    Address domain_hub;
};

// One configured domain and the latest block derived for it: none until the
// domain's registration is derived.
struct DomainDerivationState
{
    uint64_t domain_chain_id{};
    Address spoke{};
    std::optional<ProposedDomainHeader> latest_header{};
};

struct DerivedDomainBlock
{
    DomainBlock block;
    // Sender of each transaction: recovered for sequenced transactions,
    // DOMAIN_SYSTEM_RELAYER for message deliveries.
    std::vector<Address> senders;

    friend bool operator==(
        DerivedDomainBlock const &, DerivedDomainBlock const &) = default;
};

// Opens one sequenced transaction sealed to a domain's key; see
// PrivateDomainKeyring::open_transaction.
using DomainTransactionOpener = std::function<Result<byte_string>(
    uint64_t domain_chain_id, byte_string_view payload)>;

// Derives at most one block per domain from one L1 block, following
// docs/domains-protocol.md:
//   - A domain gets a block iff the L1 block registers it (genesis, block 0)
//     or holds at least one of its sequenced transactions or L1 messages,
//     whether or not any of them survives the derivation rules.
//   - A block holds the domain's sequenced transactions that survive, in L1
//     order, then one delivery per L1 message, in hub nonce order.
//   - A domain this node has no genesis for drops its hub events with an
//     error log.
// Reads no domain state. `domains` must be sorted by domain_chain_id and
// deduplicated. Fails only on a malformed hub event of a configured domain.
Result<std::vector<DerivedDomainBlock>> derive_domain_blocks(
    DomainDerivationInput const &, std::span<DomainDerivationState const>,
    DomainTransactionOpener const &);

MONAD_NAMESPACE_END
