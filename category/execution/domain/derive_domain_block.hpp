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
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derivation_error.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/inputs.hpp>

#include <cstdint>
#include <functional>
#include <optional>

MONAD_DOMAIN_NAMESPACE_BEGIN

// Price of one unit of domain gas in L1 wei, and the most gas the hub sells
// per domain per L1 block. Mirror DomainHub.DOMAIN_GAS_PRICE and
// DomainHub.DOMAIN_BLOCK_GAS_LIMIT. Every domain block has this gas limit and
// this base fee.
inline constexpr uint256_t DOMAIN_GAS_PRICE{50'000'000'000};
inline constexpr uint64_t DOMAIN_BLOCK_GAS_LIMIT = 150'000'000;

// Domain gas a fee paid to the hub buys.
uint64_t purchased_domain_gas(uint256_t const &fee);

// The domain being derived: its chain id, which its transactions carry, and
// its spoke, which its deliveries call.
struct DomainConfig
{
    uint64_t chain_id{};
    Address spoke{};
};

// Opens one sequenced transaction sealed to the domain's key; see
// PrivateDomainKey::open_transaction.
using DomainTransactionOpener =
    std::function<Result<byte_string>(byte_string_view payload)>;

// Derives at most one block of a domain from its inputs in one L1 block; see
// PROTOCOL.md in category-labs/monad-domains. `next_domain_block` is the number
// that block gets, 0 before the domain's registration is derived. Fails if the
// registration is not the domain's first input or is repeated.
Result<std::optional<DerivedDomainBlock>> derive_domain_block(
    DomainInputs const &, DomainConfig const &, uint64_t next_domain_block,
    DomainTransactionOpener const &);

MONAD_DOMAIN_NAMESPACE_END
