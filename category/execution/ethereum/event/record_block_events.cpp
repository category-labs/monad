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
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/event/record_block_events.hpp>
#include <category/execution/ethereum/validate_block.hpp>

#include <cstring>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

monad_exec_block_end *init_block_end(
    bytes32_t const &eth_block_hash, BlockHeader const &header,
    monad_exec_block_end *end_event)
{
    end_event->eth_block_hash = eth_block_hash;
    auto &exec_output = end_event->exec_output;
    memcpy(
        std::data(exec_output.logs_bloom),
        data(header.logs_bloom),
        sizeof exec_output.logs_bloom);
    exec_output.state_root = header.state_root;
    exec_output.receipts_root = header.receipts_root;
    exec_output.gas_used = header.gas_used;
    return end_event;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

void record_block_exec_start(
    bytes32_t const &bft_block_id, uint256_t const &chain_id,
    bytes32_t const &eth_parent_hash, BlockHeader const &eth_block_header,
    uint64_t block_round, uint64_t epoch, size_t txn_count)
{
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();
    if (!exec_recorder) {
        return;
    }

    monad_exec_block_start start_event;
    start_event.block_tag.id = bft_block_id;
    start_event.block_tag.block_number = eth_block_header.number;
    start_event.round = block_round;
    start_event.epoch = epoch;
    start_event.chain_id = chain_id;
    start_event.parent_eth_hash = eth_parent_hash;

    // Copy Ethereum execution input fields
    auto &exec_input = start_event.exec_input;
    exec_input.ommers_hash = eth_block_header.ommers_hash;
    exec_input.beneficiary = eth_block_header.beneficiary;
    exec_input.transactions_root = eth_block_header.transactions_root;
    exec_input.difficulty = static_cast<uint64_t>(eth_block_header.difficulty);
    exec_input.number = eth_block_header.number;
    exec_input.gas_limit = eth_block_header.gas_limit;
    exec_input.timestamp = eth_block_header.timestamp;
    exec_input.extra_data_length = size(eth_block_header.extra_data);
    memcpy(
        exec_input.extra_data.bytes,
        data(eth_block_header.extra_data),
        exec_input.extra_data_length);
    exec_input.prev_randao = eth_block_header.prev_randao;
    memcpy(
        std::data(exec_input.nonce),
        eth_block_header.nonce.data(),
        sizeof exec_input.nonce);
    exec_input.base_fee_per_gas = eth_block_header.base_fee_per_gas.value_or(0);
    exec_input.withdrawals_root =
        eth_block_header.withdrawals_root.value_or(evmc_bytes32{});
    exec_input.txn_count = txn_count;

    // Manually record the event so we can discover the sequence number to set
    // it as a flow tag for all subsequent block events
    uint64_t seqno = 0;
    uint8_t *payload;

    monad_event_descriptor *const event = exec_recorder->record_reserve(
        MONAD_EXEC_BLOCK_START, sizeof start_event, &seqno, &payload);
    if (event == nullptr) [[unlikely]] {
        return;
    }
    (void)exec_recorder->set_block_start_seqno(seqno);
    event->user[MONAD_FLOW_BLOCK_SEQNO] = seqno;
    event->user[MONAD_FLOW_TXN_ID] = 0;
    if (monad_event_ring_payload_check(exec_recorder->get_event_ring(), event))
        [[likely]] {
        memcpy(payload, &start_event, sizeof start_event);
    }
    monad_event_recorder_commit(event, seqno);
}

Result<BlockExecOutput> record_block_exec_result(Result<BlockExecOutput> result)
{
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();
    if (!exec_recorder) {
        return result;
    }

    if (result.has_error()) {
        // An execution error occurred; record a BLOCK_REJECT event if block
        // validation failed, or EVM_ERROR event for any other kind of error
        static Result<BlockExecOutput>::error_type const ref_txn_error =
            BlockError::GasAboveLimit;
        static auto const &block_err_domain = ref_txn_error.domain();
        auto const &error_domain = result.error().domain();
        auto const error_value = result.error().value();
        if (error_domain == block_err_domain) {
            exec_recorder->record(
                std::nullopt, MONAD_EXEC_BLOCK_REJECT, error_value);
        }
        else {
            monad_exec_evm_error be;
            be.domain_id = error_domain.id();
            be.status_code = error_value;
            exec_recorder->record(std::nullopt, MONAD_EXEC_EVM_ERROR, be);
        }
    }
    else {
        // Record the "block execution successful" event, BLOCK_END
        monad_exec_block_end end_event;
        BlockExecOutput const &exec_output = result.value();
        init_block_end(
            exec_output.eth_block_hash, exec_output.eth_header, &end_event);
        exec_recorder->record(std::nullopt, MONAD_EXEC_BLOCK_END, end_event);
    }
    (void)exec_recorder->set_block_start_seqno(0);
    return result;
}

MONAD_NAMESPACE_END
