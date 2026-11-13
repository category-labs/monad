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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/blob_schedule.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/revision.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <optional>
#include <span>
#include <vector>

namespace
{
    using namespace monad;

    static ankerl::unordered_dense::segmented_set<Address> const
        empty_senders_and_authorities{};
    static std::vector<Address> const empty_senders{Address{0}};
    static std::vector<std::vector<std::optional<Address>>> const
        empty_authorities{{}};
}

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

EvmRevision MonadChain::get_revision(
    uint64_t /*block_number*/, uint64_t /*timestamp*/) const
{
    MONAD_ABORT("Monad chains dispatch on get_monad_revision");
}

BlobSchedule MonadChain::get_blob_schedule(uint64_t /*timestamp*/) const
{
    return MONAD_BLOB_SCHEDULE;
}

template <typename T>
    requires is_monad_trait_v<T>
ChainContext<T> const &ChainContext<T>::debug_empty()
{
    static ChainContext<T> const ctx{
        .grandparent_senders_and_authorities = empty_senders_and_authorities,
        .parent_senders_and_authorities = empty_senders_and_authorities,
        .senders_and_authorities = empty_senders_and_authorities,
        .senders = empty_senders,
        .authorities = empty_authorities};
    return ctx;
}

EXPLICIT_MONAD_TRAITS_STRUCT(ChainContext);

template <Traits traits>
bool is_private_domain(ChainContext<traits> const &ctx)
{
    return ctx.private_domain;
}

EXPLICIT_MONAD_TRAITS(is_private_domain);

template <Traits traits>
bool is_domain_system_relayer(
    ChainContext<traits> const &ctx, Address const &sender)
{
    // DOMAIN_SYSTEM_RELAYER is the L1 system sender.
    return ctx.private_domain && sender == SYSTEM_SENDER;
}

EXPLICIT_MONAD_TRAITS(is_domain_system_relayer);

ankerl::unordered_dense::segmented_set<Address> combine_senders_and_authorities(
    std::span<Address const> const senders,
    std::span<std::vector<std::optional<Address>> const> const authorities)
{
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;

    for (Address const &sender : senders) {
        senders_and_authorities.insert(sender);
    }

    for (auto const &authorities_inner : authorities) {
        for (std::optional<Address> const &authority : authorities_inner) {
            if (authority) {
                senders_and_authorities.insert(*authority);
            }
        }
    }

    return senders_and_authorities;
}

MONAD_NAMESPACE_END
