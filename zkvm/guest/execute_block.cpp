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

#include <zkvm/guest/execute_block.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#ifdef MONAD_ZKVM_L2
    #include <category/execution/ethereum/domain_anchor.hpp>
#endif
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/ecrecover.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/ordered_trie.hpp>
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

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <variant>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using namespace monad;

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

// The one holder of SequentialExecutionToken, named as a friend by the header
// that defines it. It is a type rather than a flag so that the permission lives
// in exactly one place -- here, beside the loop whose shape is the whole
// justification for it. Defining a second
// ::monad::ZkvmSequentialExecutor anywhere else is an ODR violation, not a
// second key.
struct ZkvmSequentialExecutor
{
    static SequentialExecutionToken token()
    {
        return SequentialExecutionToken{};
    }
};

template <Traits traits>
    requires(is_evm_trait_v<traits>)
Result<ZkvmBlockOutput> execute_block_zkvm(
    Chain const &chain, Block const &block,
    // The committed bytes the transactions root is taken over -- unread on the
    // domain path, which has no such root to check.
    [[maybe_unused]] std::span<byte_string_view const> const root_transactions,
    std::span<byte_string_view const> const transaction_encodings, Db &pdb,
    vm::VM &vm, BlockHashBuffer const &block_hash_buffer,
    std::span<Address const> const recovered_senders)
{
    static_assert(traits::evm_rev() > MONAD_ETH_TANGERINE_WHISTLE);

    BlockState block_state{pdb, vm};

    std::vector<Address> senders;
    senders.reserve(block.transactions.size());
    std::vector<std::vector<std::optional<Address>>> authorities;
    authorities.reserve(block.transactions.size());
    // Each sender's signing payload is taken from the bytes the transaction
    // was decoded from instead of re-encoded from its fields;
    // rlp::signing_payload says why the two are the same bytes.
    MONAD_ASSERT(transaction_encodings.size() == block.transactions.size());
    // Handed over, or recovered here. On the domain path a transaction whose
    // sender does not recover was already dropped before the block was formed,
    // so every one left has one and there is nothing to fail on.
    bool const senders_given = !recovered_senders.empty();
    MONAD_ASSERT(
        !senders_given ||
        recovered_senders.size() == block.transactions.size());
    for (size_t i = 0; i < block.transactions.size(); ++i) {
        auto const &tx = block.transactions[i];
        if (senders_given) {
            senders.push_back(recovered_senders[i]);
        }
        else {
            auto const s = recover_address(
                tx.sc.signature,
                rlp::signing_payload(tx, transaction_encodings[i]));
            if (MONAD_UNLIKELY(!s.has_value())) {
                return TransactionError::MissingSender;
            }
            senders.push_back(*s);
        }

        std::vector<std::optional<Address>> al;
        al.reserve(tx.authorization_list.size());
        for (auto const &auth_entry : tx.authorization_list) {
            al.push_back(recover_authority(auth_entry));
        }
        authorities.push_back(std::move(al));
    }

    execute_block_header<traits>(
        block_state, block.header, /*exec_recorder=*/nullptr);

    ChainContext<traits> const
        chain_ctx{}; // chain context is empty for evm traits
    // 3. Per-tx loop, and it is serialized: exec() runs to completion, merging
    // into
    //    block_state, before the next iteration constructs its State.
    //
    //    Not "nothing else writes block_state" -- reads do.
    //    BlockState::read_account, read_storage and read_code are non-const and
    //    emplace a row on a cache miss. What makes this safe is what they
    //    write: `{result, result}`, current equal to original, the same value
    //    this State recorded through them. Both sides of every comparison
    //    can_merge makes come from that one emplace, so a non-concurrent
    //    mutation cannot make them disagree.
    //
    //    So the merge-conflict machinery ExecuteTransaction carries for the
    //    node's speculative scheduler -- the wait on `prev`, can_merge, the
    //    retry -- has nothing to detect here, and this loop says so by holding
    //    SequentialExecutionToken. Measured on block 25815100: 231 of the
    //    guest's 233 can_merge calls are that gate, the retry path runs zero
    //    times, and the check costs ~1,836 steps a transaction.
    //
    //    `prev` is still constructed because the constructor takes one; it is
    //    satisfied immediately and the sequential path never waits on it.
    BlockMetrics metrics{}; // unused; constructor requires a reference
    NoopCallTracer call_tracer{};
    trace::StateTracer state_tracer{std::monostate{}};
    std::vector<Receipt> receipts;
    receipts.reserve(block.transactions.size());

    // YP eq. 58: each transaction's gas limit must fit the remaining block gas.
    // execute_transaction asserts gas_used <= transaction gas_limit, so
    // block_gas_used stays within the block limit and subtraction cannot wrap.
    uint64_t block_gas_used = 0;

    for (uint64_t i = 0; i < block.transactions.size(); ++i) {
        if (MONAD_UNLIKELY(
                block.transactions[i].gas_limit >
                block.header.gas_limit - block_gas_used)) {
            return BlockError::InvalidGasLimit;
        }
        boost::fibers::promise<void> prev{};
        prev.set_value();
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
            chain_ctx,
            /*exec_recorder=*/nullptr};
        BOOST_OUTCOME_TRY(
            auto receipt, exec.execute(ZkvmSequentialExecutor::token()));
        block_gas_used += receipt.gas_used;
        receipts.push_back(std::move(receipt));
    }

    // The transactions and withdrawals executed above, and the receipts
    // produced, must be the ones the header commits to.
    //
    // Not on the domain path, where there is no such header. The header a
    // domain block executes against is the L1's, so its transactions root, its
    // gas_used, its receipts root and its bloom describe the L1 block and have
    // nothing to say about this domain -- comparing against them would fail
    // every block, and a header of the domain's own would only be the prover's
    // word anyway. What binds the domain's work instead is published: the state
    // commitment, and the message anchor the epilogue harvests from these very
    // receipts.
#ifndef MONAD_ZKVM_L2
    {
        // Against the committed bytes, not against a re-encoding of what was
        // decoded. That is the stronger of the two: re-encoding proves "what I
        // executed, canonically re-encoded, hashes to the committed root",
        // which admits any input whose re-encoding is canonical even where
        // decode was lossy; this proves "the bytes I read from hash to the
        // committed root", and what executed came from exactly those slices by
        // construction.
        //
        // On an L2 block the chain has one more link and is still the same
        // statement: leaf in transactions_root, in the header, in the block
        // hash this run publishes; plaintext = D_sk(leaf) under a key bound by
        // sk*G == the operator key the protocol names; and one transaction per
        // plaintext with nothing left over. The count is NOT compared there: a
        // rejected leaf is committed to and executes nothing, so the two
        // differ by however many were rejected.
        MONAD_ASSERT(root_transactions.size() == block.transactions.size());
        if (MONAD_UNLIKELY(
                ordered_trie_root(root_transactions) !=
                block.header.transactions_root)) {
            return BlockError::WrongMerkleRoot;
        }
        if (MONAD_UNLIKELY(
                to_bytes(keccak256(rlp::encode_ommers(block.ommers))) !=
                block.header.ommers_hash)) {
            return BlockError::WrongOmmersHash;
        }
        if constexpr (traits::evm_rev() >= MONAD_ETH_SHANGHAI) {
            MONAD_ASSERT(
                block.header.withdrawals_root.has_value() &&
                block.withdrawals.has_value());
            std::vector<byte_string> enc;
            enc.reserve(block.withdrawals->size());
            for (auto const &w : *block.withdrawals) {
                enc.push_back(rlp::encode_withdrawal(w));
            }
            if (MONAD_UNLIKELY(
                    ordered_trie_root(enc) != *block.header.withdrawals_root)) {
                return BlockError::WrongMerkleRoot;
            }
        }
    }

    // YP eq. 22 — cumulative gas fixup.
    uint64_t cumulative_gas_used = 0;
    for (auto &r : receipts) {
        cumulative_gas_used += r.gas_used;
        r.gas_used = cumulative_gas_used;
    }
    if (MONAD_UNLIKELY(cumulative_gas_used != block.header.gas_used)) {
        return BlockError::InvalidGasUsed;
    }
    {
        std::vector<byte_string> enc;
        enc.reserve(receipts.size());
        Receipt::Bloom bloom{};
        for (auto const &r : receipts) {
            enc.push_back(rlp::encode_receipt(r));
            for (size_t i = 0; i < bloom.size(); ++i) {
                bloom[i] |= r.bloom[i];
            }
        }
        if (MONAD_UNLIKELY(
                ordered_trie_root(enc) != block.header.receipts_root)) {
            return BlockError::WrongMerkleRoot;
        }
        if (MONAD_UNLIKELY(bloom != block.header.logs_bloom)) {
            return BlockError::WrongLogsBloom;
        }
    }
#else
    // The cumulative fixup is not a check and still has to happen: a receipt's
    // gas_used is cumulative on the wire, and the anchor is harvested from
    // these receipts.
    for (uint64_t cumulative = 0; auto &r : receipts) {
        cumulative += r.gas_used;
        r.gas_used = cumulative;
    }
#endif

    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (traits::evm_rev() >= MONAD_ETH_SHANGHAI) {
#ifdef MONAD_ZKVM_L2
        // process_withdrawal credits its recipients directly, and on this
        // chain nothing authenticates the list -- decode_domain_body rejects a
        // non-empty one for that reason. Asserted here as well because this is
        // where the harm would land, and a guard three files away is a guard
        // that can be lost.
        MONAD_ASSERT(
            !block.withdrawals.has_value() || block.withdrawals->empty());
#endif
        process_withdrawal(state, block.withdrawals);
    }

    // No requests on this chain, and gated for two reasons. The mechanism is
    // for a beacon chain this one does not have. And under Prague it would
    // make EVERY block invalid: system_call returns SystemCallMissingCode
    // unless the EIP-7002 and EIP-7251 predeploys have code, which an L2 with
    // no validators has no reason to deploy. It also builds a commitment to
    // deposit requests read out of prover-chosen logs, checked only against
    // the prover's own header -- inert today because nothing consumes it, and
    // one more prover-driven surface for a mechanism that does not apply.
#ifndef MONAD_ZKVM_L2
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
#endif

    // 4.5 The message anchor. Here and not earlier because the harvest reads
    //     `receipts`, which are only canonical once checked against the
    //     header's receipts root above; and here rather than later because the
    //     clear needs this epilogue State. Next to process_requests, the other
    //     epilogue step that consumes receipts, so the two log harvests read
    //     together.
    //
    //     Note what this CANNOT do: emit the anchor as an event. Anything
    //     store_log'd into the LAST_TX state lands in State::logs_ and is then
    //     dropped -- the receipts vector was fixed and root-checked before this
    //     State even existed. The anchor's only exits are storage and the
    //     public output, which is consistent with the contract:
    //     finalizeNamespaceMessages logs nothing either, it RETURNS the anchor.
    bytes32_t domain_anchor{};
#ifdef MONAD_ZKVM_L2
    {
        BOOST_OUTCOME_TRY(
            auto leaves, collect_domain_messages(receipts, L2_DOMAIN_SPOKE));
        // Before the root consumes the vector in place.
        auto const count = static_cast<uint64_t>(leaves.size());
        domain_anchor = sorted_pair_merkle_root(leaves);
        clear_pending_domain_messages(
            state, L2_DOMAIN_SPOKE, L2_PENDING_SLOT, count);
    }
#endif

    // No block reward on this chain, and gated rather than left to be zero.
    // apply_block_reward credits block.header.beneficiary and every ommer's
    // beneficiary -- fields the prover writes -- whenever block_reward is
    // non-zero, which is any pre-Merge revision. A static_assert in l2_config
    // forbids those, so the call would be inert; but then its safety rests on
    // a property of the revision constant rather than on a rule of the chain,
    // and an L2 has no miner, no beneficiary that means anything, and no
    // issuance. Removing the call is the rule; the static_assert is the second
    // line, not the first.
#ifndef MONAD_ZKVM_L2
    apply_block_reward<traits>(state, block);
#endif

    state.destruct_touched_dead();

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);

    // Commit accumulated state deltas to the partial trie, then read the
    // post-state root back.
    auto const released = std::move(block_state).release();
    CommitBuilder builder{block.header.number};
    pdb.commit(
        bytes32_t{}, builder, block.header, *released.state, [](BlockHeader &) {
        });

    return ZkvmBlockOutput{pdb.state_root(), domain_anchor};
}

EXPLICIT_EVM_TRAITS(execute_block_zkvm);

MONAD_NAMESPACE_END
