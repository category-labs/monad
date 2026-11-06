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

#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>

#include <cstdint>
#include <optional>

MONAD_DOMAIN_NAMESPACE_BEGIN

// A domain chain ID is 64 bits, and its low NETWORK_CHAIN_ID_BITS are the
// network chain ID.
inline constexpr uint8_t NETWORK_CHAIN_ID_BITS = 16;
inline constexpr uint64_t NETWORK_CHAIN_ID_MASK =
    (uint64_t{1} << NETWORK_CHAIN_ID_BITS) - 1;

// Private gasless transactions encode the domain in chain_id.
//
//   chain_id == network_chain_id:
//     global transaction, no domain
//   chain_id < 2^64 && (chain_id & NETWORK_CHAIN_ID_MASK) == network_chain_id:
//     private gasless transaction, full 64-bit chain_id is the domain id
//   otherwise:
//     invalid
//
// Asserts that network_chain_id <= NETWORK_CHAIN_ID_MASK.
Result<std::optional<uint64_t>> domain_from_chain_id(
    uint256_t const &chain_id, uint256_t const &network_chain_id);

MONAD_DOMAIN_NAMESPACE_END
