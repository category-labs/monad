#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/exec_event.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/result.hpp>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_types.h>
#include <monad/execution/validate_block.hpp>

#include <charconv>
#include <concepts>
#include <csignal>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <format>
#include <ranges>
#include <span>
#include <string>
#include <utility>
#include <variant>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

#include "event.hpp"

template <std::integral I>
static std::string try_parse_int_token(std::string_view s, I *i)
{
    std::from_chars_result const r = std::from_chars(begin(s), end(s), *i, 10);
    if (r.ptr != data(s) + size(s)) {
        return std::format("{} contains non-integer characters", s);
    }
    if (static_cast<int>(r.ec) != 0) {
        std::error_condition const e{r.ec};
        return std::format(
            "could not parse {} as integer: {} ({})",
            s,
            e.message(),
            e.value());
    }
    return {};
}

MONAD_NAMESPACE_BEGIN

std::variant<EventRingConfig, std::string>
try_parse_event_ring_config(std::string_view s)
{
    std::vector<std::string_view> tokens;
    EventRingConfig cfg;

    // TODO(ken): should be std::ranges::to
    for (auto t : std::views::split(s, ':')) {
        tokens.emplace_back(t);
    }

    if (size(tokens) < 1 || size(tokens) > 3) {
        return std::format(
            "input `{}` does not have "
            "expected format "
            "<file-path>[:<ring-shift>:<payload-buffer-shift>]",
            s);
    }
    cfg.event_ring_path = tokens[0];
    if (size(tokens) < 2 || tokens[1].empty()) {
        cfg.ring_shift = DEFAULT_EXECUTION_RECORDER_RING_SHIFT;
    }
    else if (auto err = try_parse_int_token(tokens[1], &cfg.ring_shift);
             !empty(err)) {
        return std::format(
            "parse error in ring_shift `{}`: {}", tokens[1], err);
    }

    if (size(tokens) < 3 || tokens[2].empty()) {
        cfg.payload_buf_shift = DEFAULT_EXECUTION_RECORDER_PAYLOAD_BUF_SHIFT;
    }
    else if (auto err = try_parse_int_token(tokens[2], &cfg.payload_buf_shift);
             !empty(err)) {
        return std::format(
            "parse error in payload_buffer_shift `{}`: {}", tokens[2], err);
    }

    return cfg;
}

int init_execution_event_recorder(EventRingConfig const &ring_config)
{
    monad_event_recorder_config const recorder_config = {
        .file_path = ring_config.event_ring_path.c_str(),
        .ring_shift = ring_config.ring_shift,
        .payload_buf_shift = ring_config.payload_buf_shift,
        .is_primary = true};
    if (int const r = monad_event_recorder_create(
            &g_monad_execution_recorder, &recorder_config)) {
        LOG_ERROR(
            "unable to initialize event system -- {}",
            monad_event_get_last_error());
        return r;
    }
    LOG_INFO("event ring `{}` created", ring_config.event_ring_path);
    return 0;
}

void record_block_exec_start(
    bytes32_t const &bft_block_id,
    MonadConsensusBlockHeader const &consensus_header, size_t txn_count)
{
    monad_event_block_exec_header *exec_header;
    (void)monad_event_next_block_flow_id(&exec_header);
    BlockHeader const &eth_block_header = consensus_header.execution_inputs;
    exec_header->bft_block_id = bft_block_id;
    exec_header->round = consensus_header.round;
    exec_header->parent_round = consensus_header.parent_round();
    exec_header->consensus_seqno = consensus_header.seqno;
    exec_header->ommers_hash = eth_block_header.ommers_hash;
    exec_header->beneficiary = eth_block_header.beneficiary;
    exec_header->difficulty =
        static_cast<uint64_t>(eth_block_header.difficulty);
    exec_header->number = eth_block_header.number;
    exec_header->gas_limit = eth_block_header.gas_limit;
    exec_header->timestamp = eth_block_header.timestamp;
    exec_header->extra_data_length = size(eth_block_header.extra_data);
    memcpy(
        exec_header->extra_data.bytes,
        data(eth_block_header.extra_data),
        exec_header->extra_data_length);
    exec_header->mix_hash = eth_block_header.prev_randao;
    memcpy(
        exec_header->nonce,
        eth_block_header.nonce.data(),
        sizeof exec_header->nonce);
    exec_header->base_fee_per_gas =
        to_bytes(eth_block_header.base_fee_per_gas.value_or(0));
    exec_header->blob_gas_used = eth_block_header.blob_gas_used.value_or(0);
    exec_header->excess_blob_gas = eth_block_header.excess_blob_gas.value_or(0);
    exec_header->parent_beacon_block_root =
        eth_block_header.parent_beacon_block_root.value_or(evmc_bytes32{});
    exec_header->txn_count = txn_count;
    record_exec_event(MONAD_EVENT_BLOCK_START, *exec_header);
}

static monad_event_block_exec_result *init_block_exec_result(
    bytes32_t const &hash, BlockHeader const &header,
    monad_event_block_exec_result *exec_result)
{
    exec_result->hash = hash;
    exec_result->parent_hash = header.parent_hash;
    memcpy(
        exec_result->logs_bloom,
        data(header.logs_bloom),
        sizeof exec_result->logs_bloom);
    exec_result->state_root = header.state_root;
    exec_result->transactions_root = header.transactions_root;
    exec_result->receipts_root = header.receipts_root;
    if (header.withdrawals_root) {
        exec_result->withdrawals_root = *header.withdrawals_root;
    }
    else {
        memset(
            exec_result->withdrawals_root.bytes,
            0,
            sizeof exec_result->withdrawals_root);
    }
    exec_result->gas_used = header.gas_used;
    return exec_result;
}

Result<BlockExecOutput> record_block_exec_result(Result<BlockExecOutput> r)
{
    if (r.has_error()) {
        // An execution error occurred; record a BLOCK_REJECT event if block
        // validation failed, or BLOCK_EXEC_ERROR event for any other kind of
        // error
        static Result<BlockExecOutput>::error_type const ref_txn_error =
            BlockError::GasAboveLimit;
        static auto const &block_err_domain = ref_txn_error.domain();
        auto const &error_domain = r.error().domain();
        auto const error_value = r.error().value();
        if (error_domain == block_err_domain) {
            record_exec_event(MONAD_EVENT_BLOCK_REJECT, error_value);
        }
        else {
            monad_event_block_exec_error ee;
            ee.domain_id = error_domain.id();
            ee.status_code = error_value;
            record_exec_event(MONAD_EVENT_BLOCK_EXEC_ERROR, ee);
        }
    }
    else {
        // Record the "block execution successful" event, BLOCK_END
        monad_event_block_exec_result exec_ended_event;
        BlockExecOutput const &exec_output = r.value();
        init_block_exec_result(
            exec_output.eth_block_hash,
            exec_output.eth_header,
            &exec_ended_event);
        record_exec_event(MONAD_EVENT_BLOCK_END, exec_ended_event);
    }
    return r;
}

MONAD_NAMESPACE_END
