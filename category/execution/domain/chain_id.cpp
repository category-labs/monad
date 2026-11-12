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

#include <category/core/assert.h>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/domain/chain_id.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>

#include <cstdint>
#include <limits>
#include <optional>

MONAD_DOMAIN_NAMESPACE_BEGIN

Result<std::optional<uint64_t>> domain_from_chain_id(
    uint256_t const &chain_id, uint256_t const &network_chain_id)
{
    MONAD_ASSERT(
        network_chain_id <= NETWORK_CHAIN_ID_MASK,
        "domain chain id suffix requires network_chain_id <= 0xFFFF");

    if (chain_id == network_chain_id) {
        return std::optional<uint64_t>{std::nullopt};
    }

    if (MONAD_UNLIKELY(chain_id > std::numeric_limits<uint64_t>::max())) {
        return TransactionError::WrongChainId;
    }
    if (MONAD_UNLIKELY(
            (chain_id & NETWORK_CHAIN_ID_MASK) != network_chain_id)) {
        return TransactionError::WrongChainId;
    }

    return std::optional<uint64_t>{static_cast<uint64_t>(chain_id)};
}

MONAD_DOMAIN_NAMESPACE_END
