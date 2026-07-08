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
#include <category/core/result.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>

#include <cstdint>
#include <optional>

// Monad namespace transactions encode the namespace in chain_id. The network
// chain id must fit in the 16-bit suffix reserved by the namespace encoding.
//
//   chain_id == network_chain_id:
//     global transaction, no namespace
//   chain_id < 2^64 && (chain_id & 0xFFFF) == network_chain_id:
//     namespace transaction, full 64-bit chain_id is the namespace id
//   otherwise:
//     invalid

MONAD_NAMESPACE_BEGIN

Result<std::optional<uint64_t>> namespace_from_chain_id(
    uint256_t const &chain_id, uint256_t const &network_chain_id);

MONAD_NAMESPACE_END
