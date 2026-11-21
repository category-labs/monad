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
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/domain_block.hpp>
#include <category/execution/domain/execute_domain_block.hpp>
#include <category/execution/domain/executor.hpp>
#include <category/execution/domain/spoke.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/db/commit_block.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/util.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// A domain always keeps its block hashes in state from its first block, so
// BLOCKHASH never falls back to a block hash buffer.
struct NoBlockHashBuffer final : BlockHashBuffer
{
    uint64_t n() const override
    {
        return 0;
    }

    bytes32_t const &get(uint64_t const n) const override
    {
        MONAD_ABORT_PRINTF("hash of domain block %lu was not in state", n);
    }
};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

PrivateDomainExecutor::PrivateDomainExecutor(
    MonadChain const &l1_chain, uint64_t const domain_chain_id,
    Address const &hub, mpt::Db &db, vm::VM &vm,
    fiber::PriorityPool &priority_pool)
    : chain_{l1_chain, domain_chain_id}
    , domain_chain_id_{domain_chain_id}
    , l1_chain_id_{static_cast<uint64_t>(l1_chain.get_chain_id())}
    , hub_{hub}
    , mpt_db_{db}
    , db_{db}
    , vm_{vm}
    , priority_pool_{priority_pool}
{
    auto const finalized = db.get_latest_finalized_version();
    if (finalized == mpt::INVALID_BLOCK_NUM) {
        return;
    }
    next_block_ = finalized + 1;
    // The spoke's code carries the domain chain id, the L1 chain id and the
    // hub, so it tells whether this db is the configured domain's.
    auto const spoke = db_.read_account(DOMAIN_SPOKE);
    auto const expected = to_bytes(
        keccak256(domain_spoke_code(domain_chain_id_, l1_chain_id_, hub_)));
    MONAD_ASSERT_PRINTF(
        spoke.has_value() && spoke->code_hash == expected,
        "db is not that of domain %lu of L1 chain %lu",
        domain_chain_id_,
        l1_chain_id_);
}

bytes32_t PrivateDomainExecutor::latest_block_hash() const
{
    MONAD_ASSERT(next_block_ > 0);
    return block_hashes_.get(next_block_ - 1);
}

std::optional<bytes32_t>
PrivateDomainExecutor::block_hash(uint64_t const number) const
{
    MONAD_ASSERT(number < next_block_);
    // The buffer keeps the latest blocks' hashes only: this reads the block's
    // header, which the db stores as the encoding the hash is of.
    auto const header = mpt_db_.find(
        mpt::concat(FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
        number);
    if (header.has_error()) {
        return std::nullopt;
    }
    return to_bytes(keccak256(header.value().node->value()));
}

template <Traits traits>
    requires is_monad_trait_v<traits>
Result<void>
PrivateDomainExecutor::execute_block(DerivedDomainBlock const &block)
{
    MONAD_ASSERT(block.senders.size() == block.transactions.size());

    bytes32_t parent_hash{};
    if (block.number > 0) {
        db_.set_block_and_prefix(block.number - 1);
        parent_hash = to_bytes(
            keccak256(rlp::encode_block_header(db_.read_eth_header())));
    }
    auto const header = domain_execution_inputs<traits>(block, parent_hash);
    // Before genesis the db is empty, and so is every read.
    BlockState block_state{db_, vm_};
    if (block.number == 0) {
        // The domain's genesis state holds its spoke.
        State state{block_state, Incarnation{0, 0}};
        deploy_domain_spoke(state, domain_chain_id_, l1_chain_id_, hub_);
        MONAD_ASSERT(block_state.can_merge(state));
        block_state.merge(state);
    }
    BOOST_OUTCOME_TRY(
        auto const receipts,
        execute_domain_block<traits>(
            chain_,
            block,
            header,
            block_state,
            NoBlockHashBuffer{},
            priority_pool_));
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
    db_.finalize(block.number, id);
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
