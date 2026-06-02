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
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

template <size_t age, size_t K>
concept valid_chain_context_buffer_age = (age < K);

template <Traits traits>
class ChainContextBuffer;

/**
 * Circular buffer of combined senders and EIP-7702 authorities for the last
 * K blocks. Use advance(senders, authorities) to obtain the context needed
 * for each block's reserve balance checks in eth_simulatev1.
 */
template <Traits traits>
    requires(is_monad_trait_v<traits>)
class ChainContextBuffer<traits>
{
    static constexpr size_t K = 3;

public:
    /// Advances the buffer with a new block's senders and authorities,
    /// discarding the oldest currently stored context, then returns a
    /// ChainContext for the given traits type. The arguments must outlive
    /// this buffer.
    ChainContext<traits> advance(
        std::vector<Address> const &senders,
        std::vector<std::vector<std::optional<Address>>> const &authorities);

private:
    template <size_t age>
        requires(valid_chain_context_buffer_age<age, K>)
    ankerl::unordered_dense::segmented_set<Address> const &get() const;

    size_t current_index_{0};
    std::array<ankerl::unordered_dense::segmented_set<Address>, K>
        senders_and_authorities_buffer_{};
    std::vector<Address> const *current_senders_{};
    std::vector<std::vector<std::optional<Address>>> const
        *current_authorities_{};
};

/**
 * Dummy buffer for EVM trait specializations that do not need chain context
 * for reserve balance checks.
 */
template <Traits traits>
    requires(is_evm_trait_v<traits>)
class ChainContextBuffer<traits>
{
public:
    ChainContext<traits> advance(
        std::vector<Address> const &,
        std::vector<std::vector<std::optional<Address>>> const &);
};

MONAD_NAMESPACE_END
