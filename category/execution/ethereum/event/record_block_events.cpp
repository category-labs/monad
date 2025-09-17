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

#include <bit>
#include <cstring>
#include <optional>

MONAD_NAMESPACE_BEGIN

void record_block_start(
    bytes32_t const &bft_block_id, uint256_t const &chain_id,
    BlockHeader const &eth_block_header, bytes32_t const &eth_parent_hash,
    uint64_t block_round, uint64_t epoch, uint128_t epoch_nano_timestamp,
    size_t txn_count,
    std::optional<monad_c_secp256k1_pubkey> const &opt_block_author,
    std::optional<monad_c_native_block_input> const &opt_monad_input)
{
    ExecutionEventRecorder *const exec_recorder = g_exec_event_recorder.get();
    if (!exec_recorder) {
        return;
    }

    ReservedExecEvent const block_start =
        exec_recorder->reserve_block_start_event();
    *block_start.payload = monad_exec_block_start{
        .block_tag{
            .id = bft_block_id,
            .block_number = eth_block_header.number,
        },
        .round = block_round,
        .epoch = epoch,
        .proposal_epoch_nanos = static_cast<__uint128_t>(epoch_nano_timestamp),
        .chain_id = chain_id,
        .author = opt_block_author.value_or(monad_c_secp256k1_pubkey{}),
        .parent_eth_hash = eth_parent_hash,
        .eth_block_input =
            {.ommers_hash = eth_block_header.ommers_hash,
             .beneficiary = eth_block_header.beneficiary,
             .transactions_root = eth_block_header.transactions_root,
             .difficulty = static_cast<uint64_t>(eth_block_header.difficulty),
             .number = eth_block_header.number,
             .gas_limit = eth_block_header.gas_limit,
             .timestamp = eth_block_header.timestamp,
             .extra_data = {}, // Variable-length, set below,
             .extra_data_length = size(eth_block_header.extra_data),
             .prev_randao = eth_block_header.prev_randao,
             .nonce = std::bit_cast<monad_c_b64>(eth_block_header.nonce),
             .base_fee_per_gas = eth_block_header.base_fee_per_gas.value_or(0),
             .withdrawals_root =
                 eth_block_header.withdrawals_root.value_or(evmc_bytes32{}),
             .txn_count = txn_count},
        .monad_block_input =
            opt_monad_input.value_or(monad_c_native_block_input{})};
    memcpy(
        block_start.payload->eth_block_input.extra_data.bytes,
        data(eth_block_header.extra_data),
        block_start.payload->eth_block_input.extra_data_length);
    exec_recorder->commit(block_start);
}

Result<BlockExecOutput> record_block_result(Result<BlockExecOutput> result)
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
            ReservedExecEvent const block_reject =
                exec_recorder->reserve_block_event<monad_exec_block_reject>(
                    MONAD_EXEC_BLOCK_REJECT);
            *block_reject.payload = static_cast<uint32_t>(error_value);
            exec_recorder->commit(block_reject);
        }
        else {
            ReservedExecEvent const evm_error =
                exec_recorder->reserve_block_event<monad_exec_evm_error>(
                    MONAD_EXEC_EVM_ERROR);
            *evm_error.payload = monad_exec_evm_error{
                .domain_id = error_domain.id(), .status_code = error_value};
            exec_recorder->commit(evm_error);
        }
    }
    else {
        // Record the "block execution successful" event, BLOCK_END
        ReservedExecEvent const block_end =
            exec_recorder->reserve_block_event<monad_exec_block_end>(
                MONAD_EXEC_BLOCK_END);
        BlockExecOutput const &exec_output = result.value();
        *block_end.payload = monad_exec_block_end{
            .eth_block_hash = exec_output.eth_block_hash,
            .exec_output = {
                .state_root = exec_output.eth_header.state_root,
                .receipts_root = exec_output.eth_header.receipts_root,
                .logs_bloom = std::bit_cast<monad_c_bloom256>(
                    exec_output.eth_header.logs_bloom),
                .gas_used = exec_output.eth_header.gas_used}};
        exec_recorder->commit(block_end);
    }
    exec_recorder->end_current_block();
    return result;
}

MONAD_NAMESPACE_END
