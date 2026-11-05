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

#include <category/execution/domain/executor.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/block_store.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derivation.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/execution.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_buffer/util.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/db/commit_block.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/util.hpp>
#include <category/vm/evm/switch_traits.hpp>

#include <boost/outcome/try.hpp>

#include <optional>
#include <utility>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

PrivateDomainExecutor::PrivateDomainExecutor(
    MonadChain const &l1_chain, uint64_t const domain_chain_id,
    DomainBlockStore const &store, mpt::Db &db, vm::VM &vm,
    fiber::PriorityPool &priority_pool)
    : l1_chain_{l1_chain}
    , domain_chain_id_{domain_chain_id}
    , store_{store}
    , db_{db}
    , vm_{vm}
    , priority_pool_{priority_pool}
    , block_hash_chain_{block_hashes_}
{
    auto const finalized = db.get_latest_finalized_version();
    if (finalized == mpt::INVALID_BLOCK_NUM) {
        return;
    }
    next_block_ = finalized + 1;
    MONAD_ASSERT(
        init_block_hash_buffer_from_triedb(db, next_block_, block_hashes_));
}

template <Traits traits>
    requires is_monad_trait_v<traits>
Result<void> PrivateDomainExecutor::execute(DomainBlock const &block)
{
    auto const &domain_header = block.header;
    // Derivation kept only transactions whose sender recovers.
    std::vector<Address> senders;
    for (auto const &sender :
         recover_senders(block.transactions, priority_pool_)) {
        MONAD_ASSERT(sender.has_value());
        senders.push_back(*sender);
    }
    DerivedDomainBlock const derived{
        .domain_chain_id = domain_chain_id_,
        .block = block,
        .senders = senders};

    auto header = execution_header<traits>(domain_header);
    if (domain_header.number > 0) {
        header.parent_hash = block_hashes_.get(domain_header.number - 1);
        db_.set_block_and_prefix(domain_header.number - 1);
    }
    // Before genesis the db is empty, and so is every read.
    BlockState block_state{db_, vm_};
    BOOST_OUTCOME_TRY(
        auto const receipts,
        execute_domain_block<traits>(
            l1_chain_,
            derived,
            header,
            block_state,
            block_hash_chain_.find_chain(domain_header.parent_id),
            priority_pool_));
    auto [state, code, _] = std::move(block_state).release();

    bytes32_t const id = domain_block_id(domain_header);
    commit_block<traits>(
        db_,
        id,
        header,
        *state,
        code,
        receipts,
        {},
        senders,
        block.transactions,
        {},
        traits::eip_4895_active() ? std::optional{std::vector<Withdrawal>{}}
                                  : std::nullopt);
    auto const eth_header = db_.read_eth_header();
    MONAD_ASSERT(
        eth_header.transactions_root == domain_header.transactions_root);
    db_.finalize(domain_header.number, id);

    block_hash_chain_.propose(
        to_bytes(keccak256(rlp::encode_block_header(eth_header))),
        domain_header.number,
        id,
        domain_header.parent_id);
    block_hash_chain_.finalize(id);
    return outcome::success();
}

Result<bool> PrivateDomainExecutor::execute_next()
{
    auto const block = store_.get(next_block_);
    if (!block.has_value()) {
        return false;
    }
    auto const rev = l1_chain_.get_monad_revision(block->header.timestamp);
    BOOST_OUTCOME_TRY([&] -> Result<void> {
        SWITCH_MONAD_TRAITS(execute, *block);
        MONAD_ABORT_PRINTF("unhandled rev %d", rev);
    }());
    ++next_block_;
    return true;
}

MONAD_DOMAIN_NAMESPACE_END
