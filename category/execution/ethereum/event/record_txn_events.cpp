#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/cpu_relax.h>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/eth_ctypes.h>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <boost/fiber/future/promise.hpp>

#include <atomic>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>

#include <string.h>

using namespace monad;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Initializes the TXN_START event payload, and returns a pointer to the
// variable-length `data` field of the transaction
std::span<std::byte const> init_txn_start(
    Transaction const &txn, Address const &sender, uint64_t ingest_epoch_nanos,
    monad_exec_txn_start *event)
{
    event->ingest_epoch_nanos = ingest_epoch_nanos;
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
    header.data_length = static_cast<uint32_t>(size(txn.data));
    header.access_list_count = 0;
    return as_bytes(std::span{txn.data});
}

// Tracks information about an accessed account, including (1) the prestate and
// the (2) the modified state if a write access modified anything, with helper
// functions to determine what was modified
struct AccountAccessInfo
{
    Address const *address;
    AccountState const *prestate; // State as it existed in original_
    AccountState const *modified_state; // Last state as it existed in current_

    bool is_read_only_access() const
    {
        return modified_state == nullptr;
    }

    std::pair<uint64_t, bool> get_nonce_modification() const
    {
        if (is_read_only_access()) {
            return {0, false};
        }
        uint64_t const prestate_nonce =
            is_dead(prestate->account_) ? 0 : prestate->account_->nonce;
        uint64_t const modified_nonce = is_dead(modified_state->account_)
                                            ? 0
                                            : modified_state->account_->nonce;
        return {modified_nonce, prestate_nonce != modified_nonce};
    }

    std::pair<uint256_t, bool> get_balance_modification() const
    {
        if (is_read_only_access()) {
            return {0, false};
        }

        uint256_t const prestate_balance =
            is_dead(prestate->account_) ? 0 : prestate->account_->balance;
        uint256_t const modified_balance =
            is_dead(modified_state->account_)
                ? 0
                : modified_state->account_->balance;
        return {modified_balance, prestate_balance != modified_balance};
    }
};

// Records a MONAD_EXEC_STORAGE_ACCESS event for all reads and writes in the
// AccountState prestate and modified maps
void record_storage_events(
    ExecutionEventRecorder *exec_recorder,
    monad_exec_account_access_context ctx, std::optional<uint32_t> opt_txn_num,
    uint32_t account_index, Address const *address,
    AccountState::Map<bytes32_t, bytes32_t> const *prestate_storage,
    AccountState::Map<bytes32_t, bytes32_t> const *modified_storage,
    bool is_transient)
{
    for (size_t index = 0; auto const &[key, value] : *prestate_storage) {
        bool is_modified = false;
        bytes32_t end_value = {};

        if (modified_storage) {
            if (auto const i = modified_storage->find(key);
                i != end(*modified_storage)) {
                end_value = i->second;
                is_modified = end_value != value;
            }
        }

        monad_exec_storage_access const storage_event = {
            .address = *address,
            .index = static_cast<uint32_t>(index++),
            .access_context = ctx,
            .modified = is_modified,
            .transient = is_transient,
            .key = key,
            .start_value = value,
            .end_value = end_value,
        };

        uint64_t seqno;
        uint8_t *payload;
        monad_event_descriptor *const event = exec_recorder->record_reserve(
            sizeof storage_event, &seqno, &payload);

        event->event_type = MONAD_EXEC_STORAGE_ACCESS;
        event->user[MONAD_FLOW_BLOCK_SEQNO] =
            exec_recorder->get_block_start_seqno();
        event->user[MONAD_FLOW_TXN_ID] = opt_txn_num.value_or(-1) + 1;
        event->user[MONAD_FLOW_ACCOUNT_INDEX] = account_index;
        memcpy(payload, &storage_event, sizeof storage_event);
        monad_event_recorder_commit(event, seqno);
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
    Account const &account = is_dead(account_info.prestate->account_)
                                 ? Account{}
                                 : *account_info.prestate->account_;

    initial_state.nonce = account.nonce;
    initial_state.balance = account.balance;
    initial_state.code_hash = account.code_hash;

    auto const [modified_balance, is_balance_modified] =
        account_info.get_balance_modification();
    auto const [modified_nonce, is_nonce_modified] =
        account_info.get_nonce_modification();

    monad_exec_account_access const access_event = {
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
    exec_recorder->record(opt_txn_num, MONAD_EXEC_ACCOUNT_ACCESS, access_event);

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
    monad_exec_account_access_list_header const list_header = {
        .entry_count = static_cast<uint32_t>(state.get_account_size()),
        .access_context = ctx};
    exec_recorder->record(
        opt_txn_num, MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER, list_header);
    uint32_t index = 0;
    state.visit_accounts([exec_recorder, opt_txn_num, ctx, &index](
                             Address const *address,
                             AccountState const *prestate,
                             AccountState const *modified_state) {
        record_account_events(
            exec_recorder,
            ctx,
            opt_txn_num,
            index++,
            AccountAccessInfo{address, prestate, modified_state});
    });
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

void record_txn_events(
    uint32_t txn_num, Transaction const &transaction, Address const &sender,
    Result<ExecutionResult> const &txn_exec_result)
{
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();
    if (exec_recorder == nullptr) {
        return;
    }

    // TXN_START
    monad_exec_txn_start txn_start_event;
    std::span<std::byte const> txn_data =
        init_txn_start(transaction, sender, 0, &txn_start_event);
    exec_recorder->record(
        txn_num, MONAD_EXEC_TXN_START, txn_start_event, txn_data);

    if (txn_exec_result.has_error()) {
        // Create a reference error so we can extract its domain with
        // `ref_txn_error.domain()`, for the purpose of checking if the
        // r.error() domain is a TransactionError. We record these as
        // TXN_REJECT events (invalid transactions) vs. all other cases
        // which are internal EVM errors (EVM_ERROR)
        static Result<ExecutionResult>::error_type const ref_txn_error =
            TransactionError::InsufficientBalance;
        static auto const &txn_err_domain = ref_txn_error.domain();
        auto const &error_domain = txn_exec_result.error().domain();
        auto const error_value = txn_exec_result.error().value();
        if (error_domain == txn_err_domain) {
            exec_recorder->record(txn_num, MONAD_EXEC_TXN_REJECT, error_value);
        }
        else {
            monad_exec_evm_error te;
            te.domain_id = error_domain.id();
            te.status_code = error_value;
            exec_recorder->record(txn_num, MONAD_EXEC_EVM_ERROR, te);
        }
        return;
    }

    // TXN_EVM_OUTPUT
    ExecutionResult const &evm_output = txn_exec_result.value();
    Receipt const &receipt = evm_output.receipt;
    monad_exec_txn_evm_output const output_event = {
        .receipt =
            {.status = receipt.status == 1,
             .log_count = static_cast<uint32_t>(size(receipt.logs)),
             .gas_used = receipt.gas_used},
        .call_frame_count = static_cast<uint32_t>(size(evm_output.call_frames)),
    };
    exec_recorder->record(txn_num, MONAD_EXEC_TXN_EVM_OUTPUT, output_event);
    for (uint32_t index = 0; auto const &log : receipt.logs) {
        monad_exec_txn_log const log_event = {
            .index = index++,
            .address = log.address,
            .topic_count = static_cast<uint8_t>(size(log.topics)),
            .data_length = static_cast<uint32_t>(size(log.data))};
        exec_recorder->record(
            txn_num,
            MONAD_EXEC_TXN_LOG,
            log_event,
            as_bytes(std::span{log.topics}),
            as_bytes(std::span{log.data}));
    }
    for (uint32_t index = 0; auto const &call_frame : evm_output.call_frames) {
        monad_exec_txn_call_frame const call_frame_event = {
            .index = index++,
            .caller = call_frame.from,
            .call_target = call_frame.to.value_or(Address{}),
            .opcode = std::to_underlying(
                get_call_frame_opcode(call_frame.type, call_frame.flags)),
            .value = call_frame.value,
            .gas = call_frame.gas,
            .gas_used = call_frame.gas_used,
            .evmc_status = std::to_underlying(call_frame.status),
            .depth = call_frame.depth,
            .input_length = size(call_frame.input),
            .return_length = size(call_frame.output),
        };
        std::span const input_bytes{
            data(call_frame.input), size(call_frame.input)};
        std::span const return_bytes{
            data(call_frame.output), size(call_frame.output)};
        exec_recorder->record(
            txn_num,
            MONAD_EXEC_TXN_CALL_FRAME,
            call_frame_event,
            as_bytes(input_bytes),
            as_bytes(return_bytes));
    }
    record_account_access_events_internal(
        exec_recorder,
        MONAD_ACCT_ACCESS_TRANSACTION,
        txn_num,
        evm_output.state);
    exec_recorder->record(txn_num, MONAD_EXEC_TXN_END);
}

// The externally-visible wrapper of the account-access-recording function that
// is called from execute_block.cpp, to record prologue and epilogue accesses;
// transaction-scope state accesses use record_txn_exec_result_events instead
void record_account_access_events(
    monad_exec_account_access_context ctx, State const &state)
{
    if (ExecutionEventRecorder *const e = g_exec_event_recorder.get()) {
        return record_account_access_events_internal(
            e, ctx, std::nullopt, state);
    }
}

MONAD_NAMESPACE_END
