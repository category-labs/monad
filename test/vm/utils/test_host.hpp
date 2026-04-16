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

#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>

namespace monad::test
{
    template <Traits traits>
    class TestHost
    {
        uint64_t tx_index_;
        NoopCallTracer noop_call_tracer_;
        State &state_;
        evmc_tx_context tx_context_;
        std::vector<Address> chain_context_senders_;
        std::vector<std::vector<std::optional<Address>>>
            chain_context_authorities_;
        ankerl::unordered_dense::segmented_set<Address>
            chain_context_senders_and_authorities_;
        ChainContext<traits> chain_context_;
        EvmcHost<traits> host_;

        ChainContext<traits> make_chain_context()
        {
            static ankerl::unordered_dense::segmented_set<Address> const
                empty_senders_and_authorities{};
            if constexpr (is_monad_trait_v<traits>) {
                return ChainContext<traits>{
                    .grandparent_senders_and_authorities =
                        empty_senders_and_authorities,
                    .parent_senders_and_authorities =
                        empty_senders_and_authorities,
                    .senders_and_authorities =
                        chain_context_senders_and_authorities_,
                    .senders = chain_context_senders_,
                    .authorities = chain_context_authorities_,
                };
            }
            else {
                return ChainContext<traits>{};
            }
        }

    public:
        TestHost(
            BlockHashBuffer const &block_hash_buffer, State &state,
            Transaction const &tx, Address const &sender,
            std::optional<uint256_t> const &base_fee_per_gas,
            std::vector<std::optional<Address>> const &authorities,
            BlockHeader const &header, Chain const &chain)
            : tx_index_{}
            , noop_call_tracer_{}
            , state_{state}
            , tx_context_{get_tx_context<traits>(
                  tx, sender, header, chain.get_chain_id())}
            , chain_context_senders_{sender}
            , chain_context_authorities_{authorities}
            , chain_context_senders_and_authorities_{combine_senders_and_authorities(
                  chain_context_senders_, chain_context_authorities_)}
            , chain_context_{make_chain_context()}
            , host_{
                  noop_call_tracer_,
                  tx_context_,
                  block_hash_buffer,
                  state,
                  tx,
                  base_fee_per_gas,
                  tx_index_,
                  chain_context_}
        {
        }

        EvmcHost<traits> &get_evmc_host()
        {
            return host_;
        }
    };
}
