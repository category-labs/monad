#include <atomic> // Must precede C headers or <stdatomic.h> causes problems

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/monad_block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/event/event.h>
#include <monad/event/event_cxx.hpp>
#include <monad/event/event_recorder.h>
#include <monad/event/event_server.h>
#include <monad/execution/validate_block.hpp>

#include <algorithm>
#include <charconv>
#include <concepts>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <format>
#include <ranges>
#include <span>
#include <string>
#include <thread>
#include <utility>

#include <pthread.h>
#include <time.h>

#include <nlohmann/json.hpp>
#include <quill/LogLevel.h>
#include <quill/Quill.h>

#include "event.hpp"

namespace fs = std::filesystem;

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

/*
 * Event server functions
 */

// Logging callback that writes to Quill
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
    extern sig_atomic_t volatile stop;
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

std::variant<EventRingConfig, std::string>
try_parse_event_ring_config(std::string_view s)
{
    std::vector<std::string_view> tokens;
    EventRingConfig cfg;

    // TODO(ken): should be std::ranges::to
    for (auto t : std::views::split(s, ':')) {
        tokens.emplace_back(t);
    }

    if (size(tokens) < 2 || size(tokens) > 4) {
        return std::format(
            "input `{}` does not have "
            "expected format "
            "<name>:<enabled>[:<ring-shift>:<payload-buffer-shift>]",
            s);
    }
    if (tokens[0] == "exec") {
        cfg.ring_type = MONAD_EVENT_RING_EXEC;
    }
    else if (tokens[0] == "trace") {
        cfg.ring_type = MONAD_EVENT_RING_TRACE;
    }
    else {
        return std::format(
            "expected ring type 'exec' or 'trace', found {}", tokens[0]);
    }

    if (tokens[1] == "1" || tokens[1] == "true") {
        cfg.enabled = true;
    }
    else if (tokens[1] == "0" || tokens[1] == "false") {
        cfg.enabled = false;
    }
    else {
        return std::format("could not parse `{}` as <enabled>", tokens[1]);
    }

    if (size(tokens) < 3 || tokens[2].empty()) {
        cfg.ring_shift = DefaultEventRingConfig[cfg.ring_type].ring_shift;
    }
    else if (auto err = try_parse_int_token(tokens[2], &cfg.ring_shift);
             !empty(err)) {
        return std::format(
            "parse error in ring_shift `{}`: {}", tokens[2], err);
    }

    if (size(tokens) < 4 || tokens[3].empty()) {
        cfg.payload_buffer_shift =
            DefaultEventRingConfig[cfg.ring_type].payload_buffer_shift;
    }
    else if (auto err =
                 try_parse_int_token(tokens[3], &cfg.payload_buffer_shift);
             !empty(err)) {
        return std::format(
            "parse error in payload_buffer_shift `{}`: {}", tokens[3], err);
    }

    return cfg;
}

std::jthread init_event_system(
    std::span<EventRingConfig const> ring_configs,
    fs::path const &event_socket_path, monad_event_server **event_server)
{
    // Configure and enable event rings
    for (EventRingConfig const &c : ring_configs) {
        if (monad_event_recorder_configure(
                c.ring_type, c.ring_shift, c.payload_buffer_shift) != 0) {
            LOG_ERROR(
                "unable to configure event ring {}:\n{}",
                std::to_underlying(c.ring_type),
                monad_event_recorder_get_last_error());
        }
        monad_event_recorder_set_enabled(c.ring_type, c.enabled);
    }

    // Launch an event server on a new thread
    return init_event_server(event_socket_path, event_server);
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
    record_event_expr(MONAD_EVENT_BLOCK_START, *exec_header);
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
            record_event_expr(
                MONAD_EVENT_BLOCK_REJECT, error_value, MONAD_EVENT_POP_SCOPE);
        }
        else {
            monad_event_block_exec_error ee;
            ee.domain_id = error_domain.id();
            ee.status_code = error_value;
            record_event_expr(
                MONAD_EVENT_BLOCK_EXEC_ERROR, ee, MONAD_EVENT_POP_SCOPE);
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
        record_event_expr(
            MONAD_EVENT_BLOCK_END, exec_ended_event, MONAD_EVENT_POP_SCOPE);
    }
    return r;
}

namespace event_cross_validation_test
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
        std::span<Receipt const> receipts, std::span<Address const> senders)
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
            Receipt const &receipt = receipts[i];

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
            txn_json["sender"] = fmt::to_string(senders[i]);

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

        auto [i_pending, _] = pending_blocks_.emplace(
            input_header.seqno, std::vector<bytes32_t>());
        std::vector<bytes32_t> &pending_block_ids = i_pending->second;
        pending_block_ids.push_back(bft_block_id);
    }

    void ExpectedDataRecorder::record_finalization(
        uint64_t consensus_seqno, bytes32_t const &bft_block_id)
    {
        auto const i_pending = pending_blocks_.find(consensus_seqno);
        if (i_pending != end(pending_blocks_)) {
            MONAD_ASSERT(array_size_ > 0);
            std::vector<bytes32_t> candidate_block_ids =
                std::move(i_pending->second);
            // Sort candidate block IDs so that abandoned events happen in
            // a well-defined order
            std::ranges::sort(candidate_block_ids);
            for (bytes32_t const &id : candidate_block_ids) {
                // Proposed block that is different from the one being
                // finalized, but with the same sequence number; this is
                // abandoned
                if (id != bft_block_id) {
                    std::string const s =
                        fmt::format(",\n{{\"Abandoned\":\"{0}\"}}", id);
                    std::fwrite(s.c_str(), s.length(), 1, file_);
                }
            }
            pending_blocks_.erase(i_pending);
        }

        if (array_size_++ > 0) {
            std::fwrite(",", 1, 1, file_);
        }
        std::string const s =
            fmt::format("\n{{\"Finalized\":\"{0}\"}}", bft_block_id);
        std::fwrite(s.c_str(), s.length(), 1, file_);
    }

} // namespace event_round_trip_test

MONAD_NAMESPACE_END
