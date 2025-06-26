#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>
#include <category/execution/ethereum/validate_block.hpp>

#include <charconv>
#include <concepts>
#include <csignal>
#include <cstdint>
#include <cstring>
#include <expected>
#include <format>
#include <memory>
#include <optional>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <utility>
#include <vector>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <unistd.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

#include "event.hpp"

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <std::integral I>
std::string try_parse_int_token(std::string_view s, I *i)
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

// Links against the global object in libmonad_execution; remains uninitialized
// if recording is disabled
extern std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

// Parse a configuration string, which has the form
//
//   <file-name>[:<descriptor-shift>:<buf-shift>]
//
// A shift can be empty, e.g., <descriptor-shift> in `my-file::30`, in which
// case the default value is used
std::expected<EventRingConfig, std::string>
try_parse_event_ring_config(std::string_view s)
{
    std::vector<std::string_view> tokens;
    EventRingConfig cfg;

    for (auto t : std::views::split(s, ':')) {
        tokens.emplace_back(t);
    }

    if (size(tokens) < 1 || size(tokens) > 3) {
        return std::unexpected(std::format(
            "input `{}` does not have "
            "expected format "
            "<file-path>[:<descriptor-shift>:<payload-buffer-shift>]",
            s));
    }
    cfg.event_ring_path = tokens[0];
    if (size(tokens) < 2 || tokens[1].empty()) {
        cfg.descriptors_shift = DEFAULT_EXEC_RING_DESCRIPTORS_SHIFT;
    }
    else if (auto err = try_parse_int_token(tokens[1], &cfg.descriptors_shift);
             !empty(err)) {
        return std::unexpected(
            std::format("parse error in ring_shift `{}`: {}", tokens[1], err));
    }

    if (size(tokens) < 3 || tokens[2].empty()) {
        cfg.payload_buf_shift = DEFAULT_EXEC_RING_PAYLOAD_BUF_SHIFT;
    }
    else if (auto err = try_parse_int_token(tokens[2], &cfg.payload_buf_shift);
             !empty(err)) {
        return std::unexpected(std::format(
            "parse error in payload_buffer_shift `{}`: {}", tokens[2], err));
    }

    return cfg;
}

int init_execution_event_recorder(EventRingConfig const &ring_config)
{
    // Create with rw-rw-r--
    constexpr mode_t mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;

    MONAD_ASSERT(!g_exec_event_recorder, "recorder initialized twice?");
    char const *ring_path = ring_config.event_ring_path.c_str();

    // Open the file and acquire a BSD-style exclusive lock on it; note there
    // is no O_TRUNC here because it might already exist and we might not own
    // it (e.g., if we're racing against another execution daemon started
    // accidentally). In that case we'll either win or lose the race to acquire
    // the lock, and will resize it only if we end up winning
    int const ring_fd = open(ring_path, O_RDWR | O_CREAT, mode);
    if (ring_fd == -1) {
        int const rc = errno;
        LOG_ERROR(
            "open failed for event ring file `{}`: {} [{}]",
            ring_path,
            strerror(rc),
            rc);
        return rc;
    }
    if (flock(ring_fd, LOCK_EX | LOCK_NB) == -1) {
        int const saved_errno = errno;
        if (saved_errno == EWOULDBLOCK) {
            pid_t owner_pid = 0;
            size_t owner_pid_size = 1;

            // Another process has the exclusive lock; find out who it is
            (void)monad_event_ring_find_writer_pids(
                ring_fd, &owner_pid, &owner_pid_size);
            if (owner_pid == 0) {
                LOG_ERROR(
                    "event ring file `{}` is owned by an unknown other process",
                    ring_path);
            }
            else {
                LOG_ERROR(
                    "event ring file `{}` is owned by pid {}",
                    ring_path,
                    owner_pid);
            }
            return saved_errno;
        }
        LOG_ERROR(
            "flock on event ring file `{}` failed: {} ({})",
            ring_path,
            strerror(saved_errno),
            saved_errno);
        (void)close(ring_fd);
        return saved_errno;
    }

    // monad_event_ring_init_simple uses fallocate(2), which is more general
    // but won't shrink the file; that's not appropriate here since we're the
    // exclusive owner; truncate it to zero first
    if (ftruncate(ring_fd, 0) == -1) {
        int const saved_errno = errno;
        LOG_ERROR(
            "ftruncate to zero failed for event ring file `{}` ({})",
            ring_path,
            strerror(saved_errno),
            saved_errno);
        (void)close(ring_fd);
        return saved_errno;
    }

    // We're the exclusive owner; initialize the event ring file
    monad_event_ring_simple_config const simple_cfg = {
        .descriptors_shift = ring_config.descriptors_shift,
        .payload_buf_shift = ring_config.payload_buf_shift,
        .context_large_pages = 0,
        .ring_type = MONAD_EVENT_RING_TYPE_EXEC,
        .metadata_hash = g_monad_exec_event_metadata_hash};
    if (int const rc =
            monad_event_ring_init_simple(&simple_cfg, ring_fd, 0, ring_path)) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        (void)close(ring_fd);
        return rc;
    }

    // Check if the underlying filesystem supports MAP_HUGETLB
    bool fs_supports_hugetlb;
    if (int const rc = monad_check_path_supports_map_hugetlb(
            ring_path, &fs_supports_hugetlb)) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        (void)close(ring_fd);
        return rc;
    }
    if (!fs_supports_hugetlb) {
        LOG_WARNING(
            "file system hosting event ring file `{}` does not support "
            "MAP_HUGETLB!",
            ring_path);
    }
    int const mmap_extra_flags =
        fs_supports_hugetlb ? MAP_POPULATE | MAP_HUGETLB : MAP_POPULATE;

    // mmap the event ring into this process' address space
    monad_event_ring exec_ring;
    if (int const rc = monad_event_ring_mmap(
            &exec_ring,
            PROT_READ | PROT_WRITE,
            mmap_extra_flags,
            ring_fd,
            0,
            ring_path)) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        (void)close(ring_fd);
        return rc;
    }

    // Create the execution recorder object
    g_exec_event_recorder =
        std::make_unique<ExecutionEventRecorder>(ring_fd, ring_path, exec_ring);
    LOG_INFO("execution event ring created: {}", ring_path);
    return 0;
}

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

    monad_event_descriptor *const event =
        exec_recorder->record_reserve(sizeof start_event, &seqno, &payload);
    (void)exec_recorder->set_block_start_seqno(seqno);
    event->event_type = MONAD_EXEC_BLOCK_START;
    event->user[MONAD_FLOW_BLOCK_SEQNO] = seqno;
    event->user[MONAD_FLOW_TXN_ID] = 0;
    memcpy(payload, &start_event, sizeof start_event);
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
