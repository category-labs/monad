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

#include "revert_transaction_generator.hpp"

#include <category/core/assert.h>
#include <category/execution/monad/validate_monad_block.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/outcome/try.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
RevertTransactionGeneratorFn revert_transaction_generator(
    bytes32_t const &block_id, bytes32_t const &parent_id, Block const &block,
    MonadChain const &chain, BlockCache &block_cache)
{
    return [&block_id, &parent_id, &block, &chain, &block_cache](
               std::vector<Address> const &senders,
               std::vector<std::vector<std::optional<Address>>> const
                   &recovered_authorities) -> Result<RevertTransactionFn> {
        BOOST_OUTCOME_TRY(static_validate_monad_senders<traits>(senders));

        // update the BlockCache with this blocks senders and authorities
        auto [entry, success] = block_cache.emplace(
            block_id,
            BlockCacheEntry{
                .block_number = block.header.number,
                .parent_id = parent_id,
                .senders_and_authorities = {}});
        MONAD_ASSERT(success, "should never be processing duplicate block");
        for (Address const &sender : senders) {
            entry->second.senders_and_authorities.insert(sender);
        }
        for (std::vector<std::optional<Address>> const &authorities :
             recovered_authorities) {
            for (std::optional<Address> const &authority : authorities) {
                if (authority.has_value()) {
                    entry->second.senders_and_authorities.insert(
                        authority.value());
                }
            }
        }

        // make the chain context, providing the parent and grandparent
        MonadChainContext chain_context{
            .grandparent_senders_and_authorities = nullptr,
            .parent_senders_and_authorities = nullptr,
            .senders_and_authorities =
                block_cache.at(block_id).senders_and_authorities,
            .senders = senders,
            .authorities = recovered_authorities};

        if (block.header.number > 1) {
            MONAD_ASSERT(
                block_cache.contains(parent_id),
                "block cache must contain parent");
            BlockCacheEntry const &parent_entry = block_cache.at(parent_id);
            chain_context.parent_senders_and_authorities =
                &parent_entry.senders_and_authorities;
            if (block.header.number > 2) {
                bytes32_t const &grandparent_id = parent_entry.parent_id;
                MONAD_ASSERT(
                    block_cache.contains(grandparent_id),
                    "block cache must contain grandparent");
                BlockCacheEntry const &grandparent_entry =
                    block_cache.at(grandparent_id);
                chain_context.grandparent_senders_and_authorities =
                    &grandparent_entry.senders_and_authorities;
            }
        }

        // return the revert transaction function to use during block execution
        return [&chain, &block, chain_context](
                   Address const &sender,
                   Transaction const &tx,
                   uint64_t const i,
                   State &state) {
            return chain.revert_transaction(
                block.header.number,
                block.header.timestamp,
                sender,
                tx,
                block.header.base_fee_per_gas.value_or(0),
                i,
                state,
                chain_context);
            return false;
        };
    };
}

EXPLICIT_MONAD_TRAITS(revert_transaction_generator);

MONAD_NAMESPACE_END
