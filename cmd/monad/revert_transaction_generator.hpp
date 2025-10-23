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

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockCacheEntry
{
    uint64_t block_number;
    bytes32_t parent_id;
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
};

using BlockCache =
    ankerl::unordered_dense::segmented_map<bytes32_t, BlockCacheEntry>;

using RevertTransactionGeneratorFn = std::function<Result<RevertTransactionFn>(
    std::vector<Address> const &,
    std::vector<std::vector<std::optional<Address>>> const &)>;

template <Traits traits>
RevertTransactionGeneratorFn revert_transaction_generator(
    bytes32_t const &block_id, bytes32_t const &parent_id, Block const &block,
    MonadChain const &chain, BlockCache &block_cache);

MONAD_NAMESPACE_END
