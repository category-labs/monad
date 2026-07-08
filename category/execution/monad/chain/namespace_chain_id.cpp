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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/monad/chain/namespace_chain_id.hpp>

#include <limits>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr uint256_t NAMESPACE_CHAIN_ID_SUFFIX_MASK{0xFFFFu};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

Result<std::optional<uint64_t>> namespace_from_chain_id(
    uint256_t const &chain_id, uint256_t const &network_chain_id)
{
    MONAD_ASSERT(
        network_chain_id <= NAMESPACE_CHAIN_ID_SUFFIX_MASK,
        "namespace chain id suffix requires network_chain_id <= 0xFFFF");

    if (chain_id == network_chain_id) {
        return std::optional<uint64_t>{std::nullopt};
    }

    if (MONAD_UNLIKELY(chain_id > std::numeric_limits<uint64_t>::max())) {
        return TransactionError::WrongChainId;
    }
    if (MONAD_UNLIKELY(
            (chain_id & NAMESPACE_CHAIN_ID_SUFFIX_MASK) != network_chain_id)) {
        return TransactionError::WrongChainId;
    }

    return std::optional<uint64_t>{static_cast<uint64_t>(chain_id)};
}

MONAD_NAMESPACE_END
