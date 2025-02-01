#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/event/event.h>
#include <monad/event/event_recorder.h>
#include <monad/event/event_server.h>
#include <monad/event/event_types.h>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/validate_block.hpp>

#include <bit>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <span>
#include <string>
#include <thread>
#include <utility>

#include <pthread.h>
#include <time.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

#include "event.hpp"

namespace fs = std::filesystem;

extern sig_atomic_t volatile stop;

template <typename T, size_t Extent>
static std::string as_hex_string(std::span<T const, Extent> s)
{
    return fmt::format("0x{:02x}", fmt::join(std::as_bytes(s), ""));
}

static std::string as_hex_string(monad::byte_string const &bs)
{
    return as_hex_string(std::span{bs});
}

template <size_t N>
static std::string as_hex_string(monad::byte_string_fixed<N> const &b)
{
    return as_hex_string(std::span{b});
}

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
    for (EventRingConfig const &c : ring_configs) {
        if (monad_event_recorder_configure(
                c.ring_type, c.ring_shift, c.payload_buffer_shift) != 0) {
            LOG_ERROR(
                "unable to configure event ring {}: {}",
                std::to_underlying(c.ring_type),
                monad_event_recorder_get_last_error());
        }
        monad_event_recorder_set_enabled(c.ring_type, c.enabled);
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

Result<BlockExecOutput> try_record_block_exec_output(
    bytes32_t const &bft_block_id,
    MonadConsensusBlockHeader const &consensus_header,
    std::span<Transaction const> txns, Result<BlockExecOutput> r,
    event_round_trip_test::ExpectedDataRecorder *rtt_recorder)
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

        if (rtt_recorder) {
            rtt_recorder->record_execution(
                bft_block_id,
                exec_output.eth_block_hash,
                consensus_header,
                exec_output.eth_header,
                txns,
                exec_output.tx_exec_results);
        }
    }
    return r;
}

EventRingConfig const DefaultEventRingConfig[] = {
    {.ring_type = MONAD_EVENT_RING_EXEC,
     .enabled = true,
     .ring_shift = MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT,
     .payload_buffer_shift = MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT},
    {.ring_type = MONAD_EVENT_RING_TRACE,
     .enabled = false,
     .ring_shift = MONAD_EVENT_DEFAULT_EXEC_RING_SHIFT,
     .payload_buffer_shift = MONAD_EVENT_DEFAULT_EXEC_PAYLOAD_BUF_SHIFT}};

namespace event_round_trip_test
{
    ExpectedDataRecorder::ExpectedDataRecorder(fs::path const &file_path)
        : array_size_{0}
    {
        file_ = std::fopen(file_path.c_str(), "w");
        if (file_ == nullptr) {
            MONAD_ABORT_PRINTF(
                "ExpectedDataRecorder cannot continue without "
                "file %s: %d (%s)",
                file_path.c_str(),
                errno,
                strerror(errno));
        }
        // Open the array
        std::fwrite("[", 1, 1, file_);
    }

    ExpectedDataRecorder::~ExpectedDataRecorder()
    {
        std::fwrite("\n]", 2, 1, file_);
        std::fclose(file_);
    }

    void ExpectedDataRecorder::record_execution(
        bytes32_t const &bft_block_id, bytes32_t const &eth_block_hash,
        MonadConsensusBlockHeader const &input_header,
        BlockHeader const &output_header, std::span<Transaction const> txns,
        std::span<ExecutionResult const> txn_exec_outputs)
    {
        nlohmann::json eth_header_json;

        eth_header_json["parentHash"] =
            fmt::to_string(output_header.parent_hash);
        eth_header_json["sha3Uncles"] =
            fmt::to_string(output_header.ommers_hash);
        eth_header_json["miner"] = fmt::to_string(output_header.beneficiary);
        eth_header_json["stateRoot"] = fmt::to_string(output_header.state_root);
        eth_header_json["transactionsRoot"] =
            fmt::to_string(output_header.transactions_root);
        eth_header_json["receiptsRoot"] =
            fmt::to_string(output_header.receipts_root);
        eth_header_json["logsBloom"] = as_hex_string(output_header.logs_bloom);
        eth_header_json["difficulty"] =
            "0x" + to_string(output_header.difficulty, 16);
        eth_header_json["number"] = output_header.number;
        eth_header_json["gasLimit"] = output_header.gas_limit;
        eth_header_json["gasUsed"] = output_header.gas_used;
        eth_header_json["timestamp"] = output_header.timestamp;
        eth_header_json["extraData"] = as_hex_string(output_header.extra_data);
        eth_header_json["mixHash"] = fmt::to_string(output_header.prev_randao);
        eth_header_json["nonce"] = as_hex_string(output_header.nonce);
        eth_header_json["baseFeePerGas"] =
            output_header.base_fee_per_gas
                ? "0x" + to_string(*output_header.base_fee_per_gas, 16)
                : fmt::to_string(bytes32_t{});
        eth_header_json["withdrawalsRoot"] = fmt::to_string(
            output_header.withdrawals_root.value_or(bytes32_t{}));

        uint64_t cumulative_gas_used = 0;
        nlohmann::json txn_array_json = nlohmann::json::array();
        for (size_t i = 0; i < size(txns); ++i) {
            Transaction const &txn = txns[i];
            Receipt const &receipt = txn_exec_outputs[i].receipt;

            nlohmann::json txn_header_json;
            txn_header_json["type"] = std::to_underlying(txn.type);
            if (txn.sc.chain_id) {
                txn_header_json["chainId"] =
                    static_cast<uint64_t>(*txn.sc.chain_id);
            }
            txn_header_json["nonce"] = txn.nonce;
            txn_header_json["gasLimit"] = txn.gas_limit;
            if (txn.to) {
                txn_header_json["to"] = fmt::to_string(*txn.to);
            }
            else {
                txn_header_json["to"] = nullptr;
            }
            txn_header_json["value"] = "0x" + to_string(txn.value, 16);
            txn_header_json["r"] = "0x" + to_string(txn.sc.r, 16);
            txn_header_json["s"] = "0x" + to_string(txn.sc.s, 16);
            txn_header_json["input"] = as_hex_string(txn.data);
            txn_header_json["hash"] = fmt::to_string(std::bit_cast<bytes32_t>(
                keccak256(rlp::encode_transaction(txn))));

            switch (txn.type) {
            case TransactionType::legacy:
                [[fallthrough]];
            case TransactionType::eip2930:
                txn_header_json["gasPrice"] =
                    static_cast<uint64_t>(txn.max_fee_per_gas);
                break;

            case TransactionType::eip1559:
                txn_header_json["maxFeePerGas"] =
                    static_cast<uint64_t>(txn.max_fee_per_gas);
                txn_header_json["maxPriorityFeePerGas"] =
                    static_cast<uint64_t>(txn.max_priority_fee_per_gas);
                break;

            default:
                MONAD_ABORT_PRINTF(
                    "unrecognized transaction type %hhu",
                    std::to_underlying(txn.type));
            }

            if (txn.type == TransactionType::legacy) {
                txn_header_json["v"] = static_cast<uint64_t>(get_v(txn.sc));
            }
            else {
                // TODO(ken): we don't produce this currently in the event
                // system
                txn_header_json["accessList"] = nlohmann::json::array();
                txn_header_json["yParity"] = txn.sc.odd_y_parity ? 1 : 0;
                txn_header_json["v"] = txn.sc.odd_y_parity ? 1 : 0;
            }

            nlohmann::json logs_array_json = nlohmann::json::array();
            for (Receipt::Log const &log : receipt.logs) {
                nlohmann::json log_json;
                log_json["address"] = fmt::to_string(log.address);
                nlohmann::json topics_array_json = nlohmann::json::array();
                for (bytes32_t const &t : log.topics) {
                    topics_array_json.push_back(fmt::to_string(t));
                }
                log_json["topics"] = std::move(topics_array_json);
                log_json["data"] = as_hex_string(log.data);
                logs_array_json.push_back(std::move(log_json));
            }

            nlohmann::json receipt_json;
            receipt_json["status"] = receipt.status;
            receipt_json["cumulativeGasUsed"] = receipt.gas_used;
            receipt_json["logs"] = std::move(logs_array_json);

            nlohmann::json txn_json;
            txn_json["index"] = i;
            txn_json["tx_header"] = std::move(txn_header_json);
            txn_json["receipt"] = std::move(receipt_json);
            txn_json["tx_gas_used"] = receipt.gas_used - cumulative_gas_used;
            txn_json["sender"] = fmt::to_string(txn_exec_outputs[i].sender);

            cumulative_gas_used = receipt.gas_used;
            txn_array_json.push_back(std::move(txn_json));
        }

        nlohmann::json j;
        j["bft_block_id"] = fmt::to_string(bft_block_id);
        j["consensus_seqno"] = input_header.seqno;
        j["eth_header"] = std::move(eth_header_json);
        j["eth_block_hash"] = fmt::to_string(eth_block_hash);
        j["txns"] = std::move(txn_array_json);

        if (array_size_++ > 0) {
            std::fwrite(",", 1, 1, file_);
        }
        std::string const s = fmt::format("\n{{\"Executed\":{0}}}", j.dump());
        std::fwrite(s.c_str(), s.length(), 1, file_);
    }

    void
    ExpectedDataRecorder::record_finalization(bytes32_t const &bft_block_id)
    {
        if (array_size_++ > 0) {
            std::fwrite(",", 1, 1, file_);
        }
        std::string const s =
            fmt::format("\n{{\"Finalized\":\"{0}\"}}", bft_block_id);
        std::fwrite(s.c_str(), s.length(), 1, file_);
    }

} // namespace event_round_trip_test

MONAD_NAMESPACE_END
