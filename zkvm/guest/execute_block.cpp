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
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_history.hpp>
#include <category/execution/ethereum/block_reward.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/ordered_trie.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/process_requests.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state_host.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/ethereum/validate_transaction_error.hpp>
#include <category/vm/evm/call_status.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using namespace monad;
using namespace monad::literals;
using BOOST_OUTCOME_V2_NAMESPACE::success;

// The transactions and withdrawals executed must be the ones the header
// commits to
template <Traits traits>
Result<void> validate_block_body(
    Block const &block,
    std::span<byte_string_view const> const raw_transactions)
{
    MONAD_ASSERT(raw_transactions.size() == block.transactions.size());
    if (MONAD_UNLIKELY(
            ordered_trie_root(raw_transactions) !=
            block.header.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(
            to_bytes(keccak256(rlp::encode_ommers(block.ommers))) !=
            block.header.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if constexpr (traits::evm_rev() >= EvmRevision::Shanghai) {
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
    return success();
}

// YP eq. 22 — cumulative gas fixup, which must sum to the header's gas used
Result<void> validate_cumulative_gas_used(
    std::vector<Receipt> &receipts, BlockHeader const &header)
{
    uint64_t cumulative_gas_used = 0;
    for (auto &r : receipts) {
        cumulative_gas_used += r.gas_used;
        r.gas_used = cumulative_gas_used;
    }
    if (MONAD_UNLIKELY(cumulative_gas_used != header.gas_used)) {
        return BlockError::InvalidGasUsed;
    }
    return success();
}

// The receipts produced must match the receipts root and logs bloom the
// header commits to
Result<void> validate_receipts(
    std::vector<Receipt> const &receipts, BlockHeader const &header)
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
    if (MONAD_UNLIKELY(ordered_trie_root(enc) != header.receipts_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(bloom != header.logs_bloom)) {
        return BlockError::WrongLogsBloom;
    }
    return success();
}

////////////////////////////////////////
// The block prologue: the native execute_block_header without its
// BlockState merge.

// EIP-4788
void set_beacon_root(State &state, BlockHeader const &header)
{
    constexpr auto BEACON_ROOTS_ADDRESS{
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02_address};
    constexpr uint256_t HISTORY_BUFFER_LENGTH{8191};

    if (state.account_exists(BEACON_ROOTS_ADDRESS)) {
        uint256_t const timestamp{header.timestamp};
        bytes32_t const k1{
            store_be_as<bytes32_t>(timestamp % HISTORY_BUFFER_LENGTH)};
        bytes32_t const k2{store_be_as<bytes32_t>(
            timestamp % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH)};
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k1, store_be_as<bytes32_t>(timestamp));
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k2, header.parent_beacon_block_root.value());
    }
}

template <Traits traits>
void execute_block_prologue(State &state, BlockHeader const &header)
{
    static_assert(traits::evm_rev() >= EvmRevision::TangerineWhistle);

    deploy_block_hash_history_contract<traits>(state);
    set_block_hash_history<traits>(state, header);

    if constexpr (traits::eip_4788_active()) {
        set_beacon_root(state, header);
    }
}

////////////////////////////////////////
// One transaction: the native ExecuteTransaction::operator() without the
// per-transaction State, the merge and the retry, and its execute_final
// without the tracers and event records.

// Refund, beneficiary credit, end-of-transaction destructs and the receipt.
// YP Eqn. 73-79.
template <Traits traits>
Receipt execute_final(
    State &state, Transaction const &tx, Address const &sender,
    BlockHeader const &header, vm::Result const &result)
{
    static_assert(traits::evm_rev() >= EvmRevision::SpuriousDragon);

    MONAD_ASSERT(result.gas_left >= 0);
    MONAD_ASSERT(result.gas_refund >= 0);
    MONAD_ASSERT(tx.gas_limit >= static_cast<uint64_t>(result.gas_left));

    auto const gas_refund = compute_gas_refund<traits>(
        tx,
        static_cast<uint64_t>(result.gas_left),
        static_cast<uint64_t>(result.gas_refund));
    auto const gas_cost =
        gas_price<traits>(tx, header.base_fee_per_gas.value_or(0));
    state.add_to_balance(sender, gas_cost * gas_refund);

    auto gas_used = tx.gas_limit - gas_refund;

    if constexpr (traits::eip_7623_active()) {
        auto const floor_gas = floor_data_gas<traits>(tx);
        if (gas_used < floor_gas) {
            auto const delta = floor_gas - gas_used;
            state.subtract_from_balance(sender, gas_cost * delta);
            gas_used = floor_gas;
        }
    }

    uint256_t const reward = calculate_txn_award<traits>(
        tx, header.base_fee_per_gas.value_or(0), gas_used);
    state.add_to_balance(header.beneficiary, reward);

    state.destruct_suicides<traits>();
    state.destruct_touched_dead();

    Receipt receipt{
        .status = result.status_code == CallStatus::Success ? 1u : 0u,
        .gas_used = gas_used,
        .type = tx.type};
    for (auto const &log : state.take_logs()) {
        receipt.add_log(log);
    }
    return receipt;
}

template <Traits traits>
Result<Receipt> execute_transaction(
    Chain const &chain, uint64_t const i, Transaction const &tx,
    Address const &sender,
    std::span<std::optional<Address> const> const authorities,
    BlockHeader const &header, BlockHashBuffer const &block_hash_buffer,
    ChainContext<traits> const &chain_ctx, State &state)
{
    BOOST_OUTCOME_TRY(static_validate_transaction<traits>(
        tx,
        header.base_fee_per_gas,
        header.excess_blob_gas,
        chain.get_chain_id(),
        chain.get_blob_schedule(header.timestamp)));

    NoopCallTracer call_tracer{};
    trace::StateTracer state_tracer{};

    BOOST_OUTCOME_TRY(validate_transaction<traits>(
        tx,
        sender,
        state,
        header.base_fee_per_gas.value_or(0),
        authorities,
        state_tracer,
        chain_ctx.mode));

    auto const tx_context = get_tx_context<traits>(
        tx,
        sender,
        header,
        chain.get_chain_id(),
        chain.get_blob_schedule(header.timestamp));
    StateHost<traits> host{
        call_tracer,
        state_tracer,
        tx_context,
        block_hash_buffer,
        state,
        tx,
        header.base_fee_per_gas,
        i,
        chain_ctx};

    ExecuteTransactionNoValidation<traits> execute{
        chain, tx, sender, authorities, header};
    auto const result = execute(state, host);
    return execute_final<traits>(state, tx, sender, header, result);
}

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
    requires(is_evm_trait_v<traits>)
Result<bytes32_t> execute_block_zkvm(
    Chain const &chain, Block const &block,
    std::span<byte_string_view const> const raw_transactions, State &state,
    BlockHashBuffer const &block_hash_buffer)
{
    static_assert(traits::evm_rev() > EvmRevision::TangerineWhistle);

    BOOST_OUTCOME_TRY(validate_block_body<traits>(block, raw_transactions));

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

    // The prologue runs in the State's initial epoch, before any
    // transaction.
    execute_block_prologue<traits>(state, block.header);

    ChainContext<traits> const
        chain_ctx{}; // chain context is empty for evm traits
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
        state.begin_transaction(i);
        BOOST_OUTCOME_TRY(
            auto receipt,
            execute_transaction<traits>(
                chain,
                i,
                block.transactions[i],
                senders[i],
                authorities[i],
                block.header,
                block_hash_buffer,
                chain_ctx,
                state));
        block_gas_used += receipt.gas_used;
        receipts.push_back(std::move(receipt));
    }

    BOOST_OUTCOME_TRY(validate_cumulative_gas_used(receipts, block.header));
    BOOST_OUTCOME_TRY(validate_receipts(receipts, block.header));

    // The post-block steps get an epoch of their own, past every
    // transaction's.
    state.begin_transaction(block.transactions.size());

    if constexpr (traits::evm_rev() >= EvmRevision::Shanghai) {
        process_withdrawal(state, block.withdrawals);
    }

    if constexpr (traits::eip_7685_active()) {
        trace::StateTracer state_tracer{};
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

    state.commit();
    return state.state_root();
}

EXPLICIT_EVM_TRAITS(execute_block_zkvm);

MONAD_NAMESPACE_END
