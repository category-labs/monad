// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/eth_ctypes.h>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state3/version_stack.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <bit>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <utility>

using namespace monad;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Initializes the TXN_HEADER_START event payload
void init_txn_header_start(
    Transaction const &txn, Address const &sender,
    monad_exec_txn_header_start *const event)
{
    event->txn_hash = to_bytes(keccak256(rlp::encode_transaction(txn)));
    event->sender = sender;
    auto &header = event->txn_header;
    header.nonce = txn.nonce;
    header.gas_limit = txn.gas_limit;
    header.max_fee_per_gas = txn.max_fee_per_gas;
    header.max_priority_fee_per_gas = txn.max_priority_fee_per_gas;
    header.value = txn.value;
    header.to = txn.to ? *txn.to : Address{};
    header.is_contract_creation = !txn.to;
    header.txn_type = std::bit_cast<monad_c_transaction_type>(txn.type);
    header.r = txn.sc.r;
    header.s = txn.sc.s;
    header.y_parity = txn.sc.y_parity == 1;
    header.chain_id = txn.sc.chain_id.value_or(0);
    header.data_length = static_cast<uint32_t>(txn.data.size());
    header.blob_versioned_hash_length =
        static_cast<uint32_t>(txn.blob_versioned_hashes.size());
    header.access_list_count = static_cast<uint32_t>(txn.access_list.size());
    header.auth_list_count =
        static_cast<uint32_t>(txn.authorization_list.size());
}

// Tracks information about an accessed account, including (1) the prestate and
// the (2) the modified state if a write access modified anything, with helper
// functions to determine what was modified
struct AccountAccessInfo
{
    Address const *address;
    OriginalAccountState const *prestate; // State as it existed in original
    AccountState const *modified_state; // Last state as it existed in current

    bool is_read_only_access() const
    {
        return modified_state == nullptr;
    }

    std::pair<uint64_t, bool> get_nonce_modification() const
    {
        if (is_read_only_access()) {
            return {0, false};
        }

        std::optional<Account> const &prestate_account =
            get_account_for_trace(*prestate);
        std::optional<Account> const &modified_account =
            get_account_for_trace(*modified_state);

        uint64_t const prestate_nonce =
            is_dead(prestate_account) ? 0 : prestate_account->nonce;
        uint64_t const modified_nonce =
            is_dead(modified_account) ? 0 : modified_account->nonce;
        return {modified_nonce, prestate_nonce != modified_nonce};
    }

    std::pair<uint256_t, bool> get_balance_modification() const
    {
        if (is_read_only_access()) {
            return {0, false};
        }

        std::optional<Account> const &prestate_account =
            get_account_for_trace(*prestate);
        std::optional<Account> const &modified_account =
            get_account_for_trace(*modified_state);

        uint256_t const prestate_balance =
            is_dead(prestate_account) ? 0 : prestate_account->balance;
        uint256_t const modified_balance =
            is_dead(modified_account) ? 0 : modified_account->balance;
        return {modified_balance, prestate_balance != modified_balance};
    }
};

/// Reserves either a block-level or transaction-level event, depending on
/// whether opt_txn_num is set or not; the account access events are allocated
/// this way, as some of them occur at system scope
template <typename T>
ReservedExecEvent<T> reserve_event(
    ExecutionEventRecorder *exec_recorder, monad_exec_event_type event_type,
    std::optional<uint32_t> opt_txn_num)
{
    return opt_txn_num
               ? exec_recorder->reserve_txn_event<T>(event_type, *opt_txn_num)
               : exec_recorder->reserve_block_event<T>(event_type);
}

// Records a MONAD_EXEC_STORAGE_ACCESS event for all reads and writes in the
// AccountState prestate and modified maps
void record_storage_events(
    ExecutionEventRecorder *exec_recorder,
    monad_exec_account_access_context ctx, std::optional<uint32_t> opt_txn_num,
    uint32_t account_index, Address const *address,
    AccountState::StorageMap const *prestate_storage,
    AccountState::StorageMap const *modified_storage, bool is_transient)
{
    for (size_t index = 0; auto const &[key, value] : *prestate_storage) {
        bool is_modified = false;
        bytes32_t end_value = {};

        if (modified_storage) {
            if (bytes32_t const *const v = modified_storage->find(key)) {
                end_value = *v;
                is_modified = end_value != value;
            }
        }

        ReservedExecEvent const storage_access =
            reserve_event<monad_exec_storage_access>(
                exec_recorder, MONAD_EXEC_STORAGE_ACCESS, opt_txn_num);
        *storage_access.payload = monad_exec_storage_access{
            .address = *address,
            .index = static_cast<uint32_t>(index),
            .access_context = ctx,
            .modified = is_modified,
            .transient = is_transient,
            .key = key,
            .start_value = value,
            .end_value = end_value,
        };
        storage_access.event->content_ext[MONAD_FLOW_ACCOUNT_INDEX] =
            account_index;
        exec_recorder->commit(storage_access);
        ++index;
    }
}

// Records an MONAD_EXEC_ACCOUNT_ACCESS event, and delegates to
// record_storage_events to record both the ordinary and transient storage
// accesses
void record_account_events(
    ExecutionEventRecorder *exec_recorder,
    monad_exec_account_access_context ctx, std::optional<uint32_t> opt_txn_num,
    uint32_t index, AccountAccessInfo const &account_info)
{
    MONAD_ASSERT(account_info.prestate);
    monad_c_eth_account_state initial_state;
    std::optional<Account> const &prestate_account =
        get_account_for_trace(*account_info.prestate);
    bool const prestate_valid = !is_dead(prestate_account);

    initial_state.nonce = prestate_valid ? prestate_account->nonce : 0;
    initial_state.balance = prestate_valid ? prestate_account->balance : 0;
    initial_state.code_hash =
        prestate_valid ? prestate_account->code_hash : NULL_HASH;

    auto const [modified_balance, is_balance_modified] =
        account_info.get_balance_modification();
    auto const [modified_nonce, is_nonce_modified] =
        account_info.get_nonce_modification();

    ReservedExecEvent const account_access =
        reserve_event<monad_exec_account_access>(
            exec_recorder, MONAD_EXEC_ACCOUNT_ACCESS, opt_txn_num);
    *account_access.payload = monad_exec_account_access{
        .index = index,
        .address = *account_info.address,
        .access_context = ctx,
        .is_balance_modified = is_balance_modified,
        .is_nonce_modified = is_nonce_modified,
        .prestate = initial_state,
        .modified_balance = modified_balance,
        .modified_nonce = modified_nonce,
        .storage_key_count =
            static_cast<uint32_t>(size(account_info.prestate->storage_)),
        .transient_count = static_cast<uint32_t>(
            size(account_info.prestate->transient_storage_))};
    exec_recorder->commit(account_access);

    auto const *const post_state_storage_map =
        account_info.is_read_only_access()
            ? nullptr
            : &account_info.modified_state->storage_;
    record_storage_events(
        exec_recorder,
        ctx,
        opt_txn_num,
        index,
        account_info.address,
        &account_info.prestate->storage_,
        post_state_storage_map,
        false);

    auto const *const post_state_transient_map =
        account_info.is_read_only_access()
            ? nullptr
            : &account_info.modified_state->transient_storage_;
    record_storage_events(
        exec_recorder,
        ctx,
        opt_txn_num,
        index,
        account_info.address,
        &account_info.prestate->transient_storage_,
        post_state_transient_map,
        true);
}

// Function that records all state accesses and changes that occurred in some
// scope, either the block prologue, block epilogue, or in the scope of some
// transaction
void record_account_access_events_internal(
    ExecutionEventRecorder *exec_recorder,
    monad_exec_account_access_context ctx, std::optional<uint32_t> opt_txn_num,
    State const &state)
{
    auto const &prestate_map = state.original();

    ReservedExecEvent const list_header =
        reserve_event<monad_exec_account_access_list_header>(
            exec_recorder, MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER, opt_txn_num);
    *list_header.payload = monad_exec_account_access_list_header{
        .entry_count = static_cast<uint32_t>(prestate_map.size()),
        .access_context = ctx};
    exec_recorder->commit(list_header);

    auto const &current_state_map = state.current();
    for (uint32_t index = 0; auto const &[address, prestate] : prestate_map) {
        AccountState const *current_state = nullptr;
        if (auto const i = current_state_map.find(address);
            i != end(current_state_map)) {
            current_state = std::addressof(i->second.recent());
        }
        record_account_events(
            exec_recorder,
            ctx,
            opt_txn_num,
            index,
            AccountAccessInfo{&address, &prestate, current_state});
        index++;
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

void record_txn_header_events(
    uint32_t const txn_num, Transaction const &transaction,
    Address const &sender,
    std::span<std::optional<Address> const> const authorities)
{
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();
    if (exec_recorder == nullptr) {
        return;
    }

    // TXN_HEADER_START
    ReservedExecEvent const txn_header_start =
        exec_recorder->reserve_txn_event<monad_exec_txn_header_start>(
            MONAD_EXEC_TXN_HEADER_START,
            txn_num,
            as_bytes(std::span{transaction.data}),
            as_bytes(std::span{transaction.blob_versioned_hashes}));
    init_txn_header_start(transaction, sender, txn_header_start.payload);
    exec_recorder->commit(txn_header_start);

    // TXN_ACCESS_LIST_ENTRY
    for (uint32_t index = 0; AccessEntry const &e : transaction.access_list) {
        ReservedExecEvent const access_list_entry =
            exec_recorder->reserve_txn_event<monad_exec_txn_access_list_entry>(
                MONAD_EXEC_TXN_ACCESS_LIST_ENTRY,
                txn_num,
                as_bytes(std::span{e.keys}));
        *access_list_entry.payload = monad_exec_txn_access_list_entry{
            .index = index,
            .entry = {
                .address = e.a,
                .storage_key_count = static_cast<uint32_t>(e.keys.size())}};
        exec_recorder->commit(access_list_entry);
        ++index;
    }

    // TXN_AUTH_LIST_ENTRY
    for (uint32_t index = 0;
         AuthorizationEntry const &e : transaction.authorization_list) {
        ReservedExecEvent const auth_list_entry =
            exec_recorder->reserve_txn_event<monad_exec_txn_auth_list_entry>(
                MONAD_EXEC_TXN_AUTH_LIST_ENTRY, txn_num);
        *auth_list_entry.payload = monad_exec_txn_auth_list_entry{
            .index = index,
            .entry =
                {
                    .chain_id = e.sc.chain_id.value_or(0),
                    .address = e.address,
                    .nonce = e.nonce,
                    .y_parity = e.sc.y_parity == 1,
                    .r = e.sc.r,
                    .s = e.sc.s,
                },
            .authority = authorities[index].value_or({}),
            .is_valid_authority = authorities[index].has_value()};
        exec_recorder->commit(auth_list_entry);
        ++index;
    }

    // TXN_HEADER_END
    exec_recorder->record_txn_marker_event(MONAD_EXEC_TXN_HEADER_END, txn_num);
}

void record_txn_output_events(
    uint32_t const txn_num, Transaction const &transaction,
    Receipt const &receipt, uint64_t gas_left,
    monad_c_eth_intrinsic_gas const &intrinsic_gas,
    std::span<CallFrame const> const call_frames, State const &txn_state)
{
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();
    if (exec_recorder == nullptr) {
        return;
    }

    // TXN_EVM_OUTPUT
    ReservedExecEvent const txn_evm_output =
        exec_recorder->reserve_txn_event<monad_exec_txn_evm_output>(
            MONAD_EXEC_TXN_EVM_OUTPUT, txn_num);
    *txn_evm_output.payload = monad_exec_txn_evm_output{
        .receipt =
            {.status = receipt.status == 1,
             .log_count = static_cast<uint32_t>(receipt.logs.size()),
             .gas_used = receipt.gas_used},
        .call_frame_count = static_cast<uint32_t>(call_frames.size())};
    exec_recorder->commit(txn_evm_output);

    // TXN_LOG
    for (uint32_t index = 0; auto const &log : receipt.logs) {
        ReservedExecEvent const txn_log =
            exec_recorder->reserve_txn_event<monad_exec_txn_log>(
                MONAD_EXEC_TXN_LOG,
                txn_num,
                as_bytes(std::span{log.topics}),
                as_bytes(std::span{log.data}));
        *txn_log.payload = monad_exec_txn_log{
            .index = index,
            .address = log.address,
            .topic_count = static_cast<uint8_t>(log.topics.size()),
            .data_length = static_cast<uint32_t>(log.data.size())};
        exec_recorder->commit(txn_log);
        ++index;
    }

    // TXN_CALL_FRAME
    for (uint32_t index = 0; auto const &call_frame : call_frames) {
        std::span const input_bytes{
            call_frame.input.data(), call_frame.input.size()};
        std::span const return_bytes{
            call_frame.output.data(), call_frame.output.size()};

        // The execution event publisher handles message call frame gas
        // accounting differently than the CallTracer API, for the top-level
        // message call.
        //
        // The RLP-encoded form of the CallFrame was designed around answering
        // RPC queries, and contains some unfortunate adjustments for the sake
        // of compatibility with popular JSON-RPC systems.
        //
        // For the top-level frame:
        //
        //   - TXN_CALL_FRAME shows the gas available to the top-level message
        //     _net of_ (after subtracting) the intrinsic gas; this is
        //     reasonable, since the intrinsic gas is not "available to" the
        //     message anymore, and because the user knows the gas limit so
        //     can compute the intrinsic gas if they want to
        //
        //   - CallFrame shows the gas available to the message _gross of_
        //     (before subtracting) the intrinsic gas; this makes it harder
        //     for them to compute the intrinsic gas
        //
        //   - TXN_CALL_FRAME shows the gas used by the top-level message to
        //     be the gas used by the EVM until the point where the message
        //     call exits
        //
        //   - CallFrame shows the gas used by the top-level message to be
        //     whatever the Receipt said it was, which for the Monad chain
        //     family, is the entire gas_limit; this makes it harder to see
        //     what the true EVM gas cost was
        uint64_t const gas_available =
            index == 0 ? transaction.gas_limit - sum(intrinsic_gas)
                       : call_frame.gas;
        uint64_t const gas_used =
            index == 0 ? gas_available - gas_left : call_frame.gas_used;

        ReservedExecEvent const txn_call_frame =
            exec_recorder->reserve_txn_event<monad_exec_txn_call_frame>(
                MONAD_EXEC_TXN_CALL_FRAME,
                txn_num,
                as_bytes(input_bytes),
                as_bytes(return_bytes));
        *txn_call_frame.payload = monad_exec_txn_call_frame{
            .index = index,
            .caller = call_frame.from,
            .call_target = call_frame.to.value_or(Address{}),
            .opcode = std::to_underlying(
                get_call_frame_opcode(call_frame.type, call_frame.flags)),
            .value = call_frame.value,
            .gas = gas_available,
            .gas_used = gas_used,
            .evmc_status = std::to_underlying(call_frame.status),
            .depth = call_frame.depth,
            .input_length = call_frame.input.size(),
            .return_length = call_frame.output.size(),
        };
        exec_recorder->commit(txn_call_frame);
        ++index;
    }

    // Account access records for the transaction
    record_account_access_events_internal(
        exec_recorder, MONAD_ACCT_ACCESS_TRANSACTION, txn_num, txn_state);

    exec_recorder->record_txn_marker_event(MONAD_EXEC_TXN_END, txn_num);
}

void record_txn_error_event(
    uint32_t const txn_num, Result<Receipt>::error_type const &txn_error)
{
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();
    if (exec_recorder == nullptr) {
        return;
    }

    // Create a reference error so we can extract its domain with
    // `ref_txn_error.domain()`, for the purpose of checking if the
    // r.error() domain is a TransactionError. We record these as
    // TXN_REJECT events (invalid transactions) vs. all other cases
    // which are internal EVM errors (EVM_ERROR)
    static Result<Receipt>::error_type const ref_txn_error =
        TransactionError::InsufficientBalance;
    static auto const &txn_err_domain = ref_txn_error.domain();
    auto const &error_domain = txn_error.domain();
    auto const error_value = txn_error.value();
    if (error_domain == txn_err_domain) {
        ReservedExecEvent const txn_reject =
            exec_recorder->reserve_txn_event<monad_exec_txn_reject>(
                MONAD_EXEC_TXN_REJECT, txn_num);
        *txn_reject.payload = static_cast<uint32_t>(error_value);
        exec_recorder->commit(txn_reject);
    }
    else {
        ReservedExecEvent const evm_error =
            exec_recorder->reserve_txn_event<monad_exec_evm_error>(
                MONAD_EXEC_EVM_ERROR, txn_num);
        *evm_error.payload = monad_exec_evm_error{
            .domain_id = error_domain.id(), .status_code = error_value};
        exec_recorder->commit(evm_error);
    }
}

// The externally-visible wrapper of the account-access-recording function that
// is called from execute_block.cpp, to record prologue and epilogue accesses;
// transaction-scope state accesses use record_txn_output_events instead
void record_account_access_events(
    monad_exec_account_access_context ctx, State const &state)
{
    if (ExecutionEventRecorder *const e = g_exec_event_recorder.get()) {
        return record_account_access_events_internal(
            e, ctx, std::nullopt, state);
    }
}

MONAD_NAMESPACE_END
