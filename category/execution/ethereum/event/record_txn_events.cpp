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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/eth_ctypes.h>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <bit>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>

using namespace monad;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Initializes the TXN_HEADER_START event payload
void init_txn_header_start(
    Transaction const &txn, Address const &sender,
    monad_exec_txn_header_start *event)
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

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

void record_txn_events(
    uint32_t txn_num, Transaction const &transaction, Address const &sender,
    std::span<std::optional<Address> const> authorities,
    Result<Receipt> const &receipt_result,
    std::span<CallFrame const> const call_frames)
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
            .authority = authorities[index].value_or(Address{}),
            .is_valid_authority = authorities[index].has_value()};
        exec_recorder->commit(auth_list_entry);
        ++index;
    }

    // TXN_HEADER_END
    exec_recorder->record_txn_marker_event(MONAD_EXEC_TXN_HEADER_END, txn_num);

    if (receipt_result.has_error()) {
        // Create a reference error so we can extract its domain with
        // `ref_txn_error.domain()`, for the purpose of checking if the
        // r.error() domain is a TransactionError. We record these as
        // TXN_REJECT events (invalid transactions) vs. all other cases
        // which are internal EVM errors (EVM_ERROR)
        static Result<Receipt>::error_type const ref_txn_error =
            TransactionError::InsufficientBalance;
        static auto const &txn_err_domain = ref_txn_error.domain();
        auto const &error_domain = receipt_result.error().domain();
        auto const error_value = receipt_result.error().value();
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
        return;
    }

    // TXN_EVM_OUTPUT
    Receipt const &receipt = receipt_result.value();
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
            .gas = call_frame.gas,
            .gas_used = call_frame.gas_used,
            .evmc_status = std::to_underlying(call_frame.status),
            .depth = call_frame.depth,
            .input_length = call_frame.input.size(),
            .return_length = call_frame.output.size(),
        };
        exec_recorder->commit(txn_call_frame);
        ++index;
    }

    exec_recorder->record_txn_marker_event(MONAD_EXEC_TXN_END, txn_num);
}

MONAD_NAMESPACE_END
