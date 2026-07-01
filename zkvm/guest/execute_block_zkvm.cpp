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

#include <zkvm/guest/execute_block_zkvm.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/execute_block_header.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <optional>
#include <utility>
#include <variant>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using namespace monad;

// EIP-4895 — mirrors the anonymous-namespace helper in execute_block.cpp.
// Local copy because the original is TU-private; the body is short enough
// that re-implementing here is cheaper than promoting it to a header.
void process_withdrawal(
    State &state, std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    if (withdrawals.has_value()) {
        for (auto const &w : withdrawals.value()) {
            state.add_to_balance(
                w.recipient, uint256_t{w.amount} * uint256_t{1'000'000'000u});
        }
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

template <Traits traits>
Result<bytes32_t> execute_block_zkvm(
    Chain const &chain, Block const &block, PartialTrieDb &pdb, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer,
    ChainContext<traits> const &chain_ctx)
{
    static_assert(traits::evm_rev() > MONAD_ETH_TANGERINE_WHISTLE);

    BlockState block_state{pdb, vm};

    // 1. Sequential sender / authority recovery — replaces recover_senders
    //    / recover_authorities (execute_block.cpp:108-171), which dispatch
    //    via fiber::PriorityPool. Sequentially we just call recover_sender
    //    / recover_authority directly.
    std::vector<Address> senders;
    senders.reserve(block.transactions.size());
    std::vector<std::vector<std::optional<Address>>> authorities;
    authorities.reserve(block.transactions.size());
    for (auto const &tx : block.transactions) {
        auto const s = recover_sender(tx);
        if (MONAD_UNLIKELY(!s.has_value())) {
            return TransactionError::MissingSender;
        }
        senders.push_back(*s);

        std::vector<std::optional<Address>> al;
        al.reserve(tx.authorization_list.size());
        for (auto const &auth_entry : tx.authorization_list) {
            al.push_back(recover_authority(auth_entry));
        }
        authorities.push_back(std::move(al));
    }

    // 2. Block-header prelude — reused unchanged.
    execute_block_header<traits>(block_state, block.header);

    // 3. Per-tx loop. ExecuteTransaction waits on `prev` to gate the merge
    //    step on the previous tx finishing — we're sequential, so the zkVM
    //    boost.fiber shadow makes the promise/future a no-op.
    BlockMetrics metrics{}; // unused; constructor requires a reference
    NoopCallTracer call_tracer{};
    trace::StateTracer state_tracer{std::monostate{}};
    boost::fibers::promise<void> prev{}; // no-op under the zkVM shadow
    std::vector<Receipt> receipts;
    receipts.reserve(block.transactions.size());

    for (uint64_t i = 0; i < block.transactions.size(); ++i) {
        ExecuteTransaction<traits> exec{
            chain,
            i,
            block.transactions[i],
            senders[i],
            authorities[i],
            block.header,
            block_hash_buffer,
            block_state,
            metrics,
            prev,
            call_tracer,
            state_tracer,
            chain_ctx};
        BOOST_OUTCOME_TRY(auto receipt, exec());
        receipts.push_back(std::move(receipt));
    }

    // YP eq. 22 — cumulative gas fixup. Mirrors execute_block.cpp:292-296.
    uint64_t cumulative_gas_used = 0;
    for (auto &r : receipts) {
        cumulative_gas_used += r.gas_used;
        r.gas_used = cumulative_gas_used;
    }

    // 4. Epilogue: withdrawals, requests-hash check, block reward — same
    //    State / merge dance as execute_block.cpp:338-363.
    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (traits::evm_rev() >= MONAD_ETH_SHANGHAI) {
        process_withdrawal(state, block.withdrawals);
    }

    if constexpr (traits::eip_7685_active()) {
        BOOST_OUTCOME_TRY(
            auto const computed_requests_hash,
            process_requests<traits>(
                chain,
                state,
                block_hash_buffer,
                block.header,
                state_tracer,
                chain_ctx,
                receipts));
        MONAD_ASSERT(block.header.requests_hash.has_value());
        if (MONAD_UNLIKELY(
                computed_requests_hash != block.header.requests_hash.value())) {
            return BlockError::InvalidRequestsHash;
        }
    }

    apply_block_reward<traits>(state, block);

    state.destruct_touched_dead();

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);

    // 5. Commit accumulated state deltas to the partial trie, then read the
    //    post-state root back. No populate_header — the zkVM doesn't care
    //    about the live header's state_root / receipts_root / etc.; the
    //    output is the trie root we just computed.
    auto released = std::move(block_state).release();
    CommitBuilder builder{block.header.number};
    pdb.commit(
        bytes32_t{}, builder, block.header, *released.state, [](BlockHeader &) {
        });

    return pdb.state_root();
}

EXPLICIT_TRAITS(execute_block_zkvm);

MONAD_NAMESPACE_END
