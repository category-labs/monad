#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/result.hpp>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_server.h>
#include <monad/event/event_types.h>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>

#include <bit>
#include <csignal>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <span>
#include <thread>

#include <pthread.h>
#include <time.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

#include "event.hpp"

namespace fs = std::filesystem;

extern sig_atomic_t volatile stop;

/*
 * Event server functions
 */

static void monad_event_server_logger(int severity, char const *msg, void *ctx)
{
    constexpr quill::LogLevel syslog_to_quill_levels[] = {
        quill::LogLevel::Critical,
        quill::LogLevel::Critical,
        quill::LogLevel::Critical,
        quill::LogLevel::Error,
        quill::LogLevel::Warning,
        quill::LogLevel::Info,
        quill::LogLevel::Info,
        quill::LogLevel::Debug};
    auto *const logger = static_cast<quill::Logger *>(ctx);
    if (!logger->should_log(syslog_to_quill_levels[severity])) {
        return;
    }
    QUILL_DYNAMIC_LOG(logger, syslog_to_quill_levels[severity], "{}", msg);
}

static void event_server_thread_main(
    std::stop_token const token, monad_event_server *server)
{
    pthread_setname_np(pthread_self(), "event_server");
    timespec const timeout{.tv_sec = 1, .tv_nsec = 30'000'000};
    while (!token.stop_requested() && stop == 0) {
        (void)monad_event_server_process_work(
            server, &timeout, nullptr, nullptr);
    }
}

static std::jthread init_event_server(
    fs::path const &event_socket_path, monad_event_server **event_server)
{
    int srv_rc;
    monad_event_server_options event_server_opts = {
        .log_fn = monad_event_server_logger,
        .log_context = quill::get_root_logger(),
        .socket_path = MONAD_EVENT_DEFAULT_SOCKET_PATH};
    // Note the comma operator because c_str() is only temporary
    event_server_opts.socket_path = event_socket_path.c_str(),
    srv_rc = monad_event_server_create(&event_server_opts, event_server);
    if (srv_rc != 0) {
        // TODO(ken): should this be an exception?
        LOG_ERROR("event server initialization error, server is disabled");
        return {};
    }

    // Launch the event server as a separate thread
    return std::jthread{event_server_thread_main, *event_server};
}

MONAD_NAMESPACE_BEGIN

std::jthread init_event_system(
    std::span<EventRingConfig const, MONAD_EVENT_RING_COUNT> ring_configs,
    fs::path const &event_socket_path, monad_event_server **event_server)
{
    for (uint8_t i = 0; EventRingConfig const &c : ring_configs) {
        monad_event_recorder_set_enabled(
            static_cast<monad_event_ring_type>(i), c.enabled);
    }

    // Host an event server on a separate thread, so external clients can
    // connect
    return init_event_server(event_socket_path, event_server);
}

/*
 * Block begin / end helper functions reused by runloop_{ethereum,monad}.cpp
 */

monad_event_block_exec_header *init_block_exec_header(
    bytes32_t const &bft_block_id,
    MonadConsensusBlockHeader const &consensus_header, size_t txn_count,
    monad_event_block_exec_header *exec_header)
{
    BlockHeader const &eth_block_header = consensus_header.execution_inputs;
    exec_header->bft_block_id = bft_block_id;
    exec_header->round = consensus_header.round;
    exec_header->consensus_seqno = consensus_header.seqno;
    exec_header->parent_hash = eth_block_header.parent_hash;
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
    exec_header->base_fee_per_gas = *std::bit_cast<evmc_bytes32 const *>(
        as_bytes(eth_block_header.base_fee_per_gas.value_or(0)));
    exec_header->blob_gas_used = eth_block_header.blob_gas_used.value_or(0);
    exec_header->excess_blob_gas = eth_block_header.excess_blob_gas.value_or(0);
    exec_header->parent_beacon_block_root =
        eth_block_header.parent_beacon_block_root.value_or(evmc_bytes32{});
    exec_header->txn_count = txn_count;
    return exec_header;
}

monad_event_block_exec_result *init_block_exec_result(
    bytes32_t const &hash, BlockHeader const &header,
    monad_event_block_exec_result *exec_result)
{
    exec_result->hash = hash;
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

Result<BlockExecOutput> try_record_block_exec_output(Result<BlockExecOutput> r)
{
    if (r.has_error()) {
        // An execution error occurred: record a BLOCK_REJECT (if validation
        // failed) or BLOCK_EXEC_ERROR event (if we get any other kind of error
        // code)
        static Result<ExecutionResult>::error_type const ref_txn_error =
            BlockError::GasAboveLimit;
        static auto const &block_err_domain = ref_txn_error.domain();
        auto const &error_domain = r.error().domain();
        auto const error_value = r.error().value();
        if (error_domain == block_err_domain) {
            MONAD_EVENT_EXPR(
                MONAD_EVENT_BLOCK_REJECT, MONAD_EVENT_POP_SCOPE, error_value);
        }
        else {
            monad_event_block_exec_error ee;
            ee.domain_id = error_domain.id();
            ee.status_code = error_value;
            MONAD_EVENT_EXPR(
                MONAD_EVENT_BLOCK_EXEC_ERROR, MONAD_EVENT_POP_SCOPE, ee);
        }
    }
    else {
        // Record the successful termination of block execution
        monad_event_block_exec_result exec_ended_event;
        BlockExecOutput const &exec_output = r.value();
        init_block_exec_result(
            exec_output.eth_block_hash,
            exec_output.eth_header,
            &exec_ended_event);
        MONAD_EVENT_EXPR(
            MONAD_EVENT_BLOCK_END, MONAD_EVENT_POP_SCOPE, exec_ended_event);
    }
    monad_event_recorder_end_block();
    return r;
}

MONAD_NAMESPACE_END
