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
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/execution_modalities.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class BlockState;

namespace fiber
{
    class PriorityPool;
}

MONAD_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

struct DerivedDomainBlock;

// The chain a private domain executes as: the L1's revisions, under the
// domain's chain id, which CHAINID returns and transactions must carry.
class DomainChain final : public MonadChain
{
    MonadChain const &l1_chain_;
    uint64_t domain_chain_id_;

public:
    DomainChain(MonadChain const &l1_chain, uint64_t domain_chain_id);

    uint256_t get_chain_id() const override;
    monad_revision get_monad_revision(uint64_t timestamp) const override;
    // Empty: a domain starts with no accounts.
    GenesisState get_genesis_state() const override;
};

// The context a private domain's transactions execute in, given those of
// its block: their senders, their authorities and both combined.
template <Traits traits>
    requires is_monad_trait_v<traits>
ChainContext<traits> domain_chain_context(
    ankerl::unordered_dense::segmented_set<Address> const
        &senders_and_authorities,
    std::vector<Address> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities,
    ExecutionMode const &mode = {});

// The Ethereum header a domain block executes under at revision `traits`,
// given the hash of its parent block's header, which is zero for block 0.
// Execution fills in transactions_root, state_root, receipts_root, logs_bloom
// and gas_used.
template <Traits traits>
    requires is_monad_trait_v<traits>
BlockHeader domain_execution_inputs(
    DerivedDomainBlock const &, bytes32_t const &parent_hash);

// Executes a derived domain block's transactions in order under the private
// domain rules, which exist from MONAD_TEN: an earlier revision aborts.
// `block_state` holds the domain's state as of the previous
// block, `header` is the block's domain_execution_inputs, and `block_hashes`
// serves BLOCKHASH. Returns one receipt per transaction.
template <Traits traits>
    requires is_monad_trait_v<traits>
Result<std::vector<Receipt>> execute_domain_block(
    DomainChain const &chain, DerivedDomainBlock const &,
    BlockHeader const &header, BlockState &,
    BlockHashBuffer const &block_hashes, fiber::PriorityPool &);

MONAD_DOMAIN_NAMESPACE_END
