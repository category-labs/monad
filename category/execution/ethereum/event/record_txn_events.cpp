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
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>

#include <bit>
#include <cstddef>
#include <cstdint>
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

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

void record_txn_events(
    uint32_t txn_num, Transaction const &transaction, Address const &sender,
    Result<Receipt> const &receipt_result,
    std::span<CallFrame const> call_frames)
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
    Receipt const &receipt = receipt_result.value();
    monad_exec_txn_evm_output const output_event = {
        .receipt =
            {.status = receipt.status == 1,
             .log_count = static_cast<uint32_t>(size(receipt.logs)),
             .gas_used = receipt.gas_used},
        .call_frame_count = static_cast<uint32_t>(size(call_frames)),
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
    for (uint32_t index = 0; auto const &call_frame : call_frames) {
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
    exec_recorder->record(txn_num, MONAD_EXEC_TXN_END);
}

MONAD_NAMESPACE_END
