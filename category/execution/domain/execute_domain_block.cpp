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
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/execute_domain_block.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <ankerl/unordered_dense.h>

#include <memory>
#include <variant>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

DomainChain::DomainChain(
    MonadChain const &l1_chain, uint64_t const domain_chain_id)
    : l1_chain_{l1_chain}
    , domain_chain_id_{domain_chain_id}
{
}

uint256_t DomainChain::get_chain_id() const
{
    return domain_chain_id_;
}

monad_revision DomainChain::get_monad_revision(uint64_t const timestamp) const
{
    return l1_chain_.get_monad_revision(timestamp);
}

GenesisState DomainChain::get_genesis_state() const
{
    return GenesisState{};
}

template <Traits traits>
    requires is_monad_trait_v<traits>
BlockHeader execution_header(DerivedDomainBlock const &block)
{
    BlockHeader header{
        .prev_randao = block.prev_randao,
        .number = block.number,
        .gas_limit = DOMAIN_BLOCK_GAS_LIMIT,
        .timestamp = block.timestamp,
        .extra_data = byte_string(32, 0),
        .beneficiary = Address{},
        .base_fee_per_gas = DOMAIN_GAS_PRICE};
    // Fork fields are present iff the revision has them, with the values of a
    // block without blobs, withdrawals or requests.
    if constexpr (traits::eip_4895_active()) {
        header.withdrawals_root = NULL_ROOT;
    }
    if constexpr (traits::eip_4844_header_active()) {
        header.blob_gas_used = 0;
        header.excess_blob_gas = 0;
    }
    if constexpr (traits::eip_4788_active()) {
        header.parent_beacon_block_root = bytes32_t{};
    }
    if constexpr (traits::eip_7685_header_active()) {
        header.requests_hash = compute_requests_hash({});
    }
    if constexpr (traits::eip_7843_active()) {
        header.block_access_list_hash = bytes32_t{};
        // Copied from the L1 block, whose header always has it at this
        // revision.
        MONAD_ASSERT(block.slot_number.has_value());
        header.slot_number = block.slot_number;
    }
    return header;
}

EXPLICIT_MONAD_TRAITS(execution_header);

template <Traits traits>
    requires is_monad_trait_v<traits>
Result<std::vector<Receipt>> execute_domain_block(
    DomainChain const &chain, DerivedDomainBlock const &derived,
    BlockHeader const &header, BlockState &block_state,
    BlockHashBuffer const &block_hashes, fiber::PriorityPool &priority_pool)
{
    auto const &transactions = derived.transactions;
    MONAD_ASSERT(derived.senders.size() == transactions.size());
    auto const authorities = recover_authorities(transactions, priority_pool);
    // Reserve balance checks, the only users of the sender sets, are off in
    // a private domain.
    ankerl::unordered_dense::segmented_set<Address> const none;
    auto const senders_and_authorities =
        combine_senders_and_authorities(derived.senders, authorities);
    ChainContext<traits> const chain_ctx{
        .grandparent_senders_and_authorities = none,
        .parent_senders_and_authorities = none,
        .senders_and_authorities = senders_and_authorities,
        .senders = derived.senders,
        .authorities = authorities,
        .private_domain = true};

    std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
    std::vector<std::unique_ptr<trace::StateTracer>> state_tracers;
    for (size_t i = 0; i < transactions.size(); ++i) {
        call_tracers.push_back(std::make_unique<NoopCallTracer>());
        state_tracers.push_back(
            std::make_unique<trace::StateTracer>(std::monostate{}));
    }
    BlockMetrics block_metrics;
    return execute_block_transactions<traits>(
        chain,
        header,
        transactions,
        derived.senders,
        authorities,
        block_state,
        block_hashes,
        priority_pool.fiber_group(),
        block_metrics,
        call_tracers,
        state_tracers,
        chain_ctx,
        nullptr,
        false);
}

EXPLICIT_MONAD_TRAITS(execute_domain_block);

MONAD_DOMAIN_NAMESPACE_END
