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
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/execute_domain_block.hpp>
#include <category/execution/domain/executor.hpp>
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
    MonadChain const &l1_chain, uint64_t const domain_chain_id, mpt::Db &db,
    vm::VM &vm, fiber::PriorityPool &priority_pool)
    : chain_{l1_chain, domain_chain_id}
    , db_{db}
    , vm_{vm}
    , priority_pool_{priority_pool}
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
Result<void>
PrivateDomainExecutor::execute_block(DerivedDomainBlock const &block)
{
    MONAD_ASSERT(block.senders.size() == block.transactions.size());

    auto header = execution_header<traits>(block);
    if (block.number > 0) {
        header.parent_hash = block_hashes_.get(block.number - 1);
        db_.set_block_and_prefix(block.number - 1);
    }
    // Before genesis the db is empty, and so is every read.
    BlockState block_state{db_, vm_};
    BOOST_OUTCOME_TRY(
        auto const receipts,
        execute_domain_block<traits>(
            chain_, block, header, block_state, block_hashes_, priority_pool_));
    auto [state, code, _] = std::move(block_state).release();

    // The block is finalized at once, so its proposal id only has to be
    // unique per height, and nonzero.
    bytes32_t const id{block.number + 1};
    commit_block<traits>(
        db_,
        id,
        header,
        *state,
        code,
        receipts,
        {},
        block.senders,
        block.transactions,
        {},
        traits::eip_4895_active() ? std::optional{std::vector<Withdrawal>{}}
                                  : std::nullopt);
    auto const eth_header = db_.read_eth_header();
    db_.finalize(block.number, id);
    block_hashes_.set(
        block.number,
        to_bytes(keccak256(rlp::encode_block_header(eth_header))));
    return outcome::success();
}

Result<void> PrivateDomainExecutor::execute(DerivedDomainBlock const &block)
{
    auto const number = block.number;
    MONAD_ASSERT_PRINTF(
        number == next_block_,
        "domain block %lu is not the next block, %lu",
        number,
        next_block_);
    auto const rev = chain_.get_monad_revision(block.timestamp);
    BOOST_OUTCOME_TRY([&] -> Result<void> {
        SWITCH_MONAD_TRAITS(execute_block, block);
        MONAD_ABORT_PRINTF("unhandled rev %d", rev);
    }());
    ++next_block_;
    return outcome::success();
}

MONAD_DOMAIN_NAMESPACE_END
