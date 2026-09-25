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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/rpc/chain_context_buffer.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

template <size_t age>
    requires(valid_chain_context_buffer_age<age, 3>)
ankerl::unordered_dense::segmented_set<Address> const &
ChainContextBuffer::get() const
{
    return senders_and_authorities_buffer_[(current_index_ + age) % K];
}

template <Traits traits>
ChainContext<traits> ChainContextBuffer::advance(
    std::vector<Address> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities)
{
    current_index_ = current_index_ == 0 ? K - 1 : current_index_ - 1;
    current_senders_ = &senders;
    current_authorities_ = &authorities;
    senders_and_authorities_buffer_[current_index_] =
        combine_senders_and_authorities(senders, authorities);

    if constexpr (is_monad_trait_v<traits>) {
        return ChainContext<traits>{
            .grandparent_senders_and_authorities = get<2>(),
            .parent_senders_and_authorities = get<1>(),
            .senders_and_authorities = get<0>(),
            .senders = *current_senders_,
            .authorities = *current_authorities_,
        };
    }
    else {
        return ChainContext<traits>{};
    }
}

EXPLICIT_TRAITS_MEMBER(ChainContextBuffer::advance);

MONAD_NAMESPACE_END
