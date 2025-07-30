#pragma once

/**
 * @file
 *
 * This file defines the execution event recorder, which is a global object.
 * It is up to the driver code using this library to configure it, otherwise
 * recording will remain disabled.
 */

#include <category/core/config.hpp>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#include <array>
#include <atomic>
#include <bit>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>

#include <string.h>

MONAD_NAMESPACE_BEGIN

/// All execution event recording goes through this object; it owns the
/// `monad_event_recorder` object, the execution event ring memory mapping, and
/// holds the event ring's file descriptor open (so that the flock(2) remains in
/// place); it also keeps track of the block flow ID -- the sequence number of
/// the BLOCK_START event, copied into all subsequent block-level events
class ExecutionEventRecorder
{
public:
    explicit ExecutionEventRecorder(
        int ring_fd, std::string_view ring_path, monad_event_ring const &);

    ~ExecutionEventRecorder();

    uint64_t get_block_start_seqno() const
    {
        return block_start_seqno_;
    }

    uint64_t set_block_start_seqno(uint64_t seqno)
    {
        std::swap(block_start_seqno_, seqno);
        return seqno;
    }

    // Some events need "customized" recording (e.g., they need to modify
    // the event descriptor manually, or do some time-sensitive work between
    // descriptor reservation and a potentially-expensive payload memcpy);
    // such customized recording calls this method and manually finishes the
    // recording process; in the general case, recording should instead call
    // one of the "all-in-one" `record` overloads below, when possible
    monad_event_descriptor *
    record_reserve(size_t payload_size, uint64_t *seqno, uint8_t **payload)
    {
        return monad_event_recorder_reserve(
            &exec_recorder_, payload_size, seqno, payload);
    }

    /*
     * `record` overloads; these differ in how the event payload is specified
     */

    /// Record an execution event with a payload specified by a C-style
    /// (pointer, length) pair
    void record(
        std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
        void const *payload, size_t payload_length)
    {
        uint64_t seqno;
        uint8_t *payload_buf;

        monad_event_descriptor *const event = monad_event_recorder_reserve(
            &exec_recorder_, payload_length, &seqno, &payload_buf);
        if (payload_length > 0) {
            memcpy(payload_buf, payload, payload_length);
        }
        event->event_type = std::to_underlying(type);
        event->user[MONAD_FLOW_BLOCK_SEQNO] = block_start_seqno_;
        event->user[MONAD_FLOW_TXN_ID] = opt_txn_num.value_or(-1) + 1;
        monad_event_recorder_commit(event, seqno);
    }

    /// Record an execution event with no payload
    void record(std::optional<uint32_t> opt_txn_num, monad_exec_event_type type)
    {
        return record(opt_txn_num, type, nullptr, 0);
    }

    /// Record an execution event whose payload is described by some
    /// memcpy-able type T
    template <typename T>
        requires std::is_trivially_copyable_v<T>
    void record(
        std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
        T const &payload)
    {
        return record(opt_txn_num, type, &payload, sizeof payload);
    }

    /// Record an execution event whose payload is described by a memcpy-able
    /// type T, followed by a variadic number of byte buffer arguments, each
    /// described by a `std::span<std::byte const>` (gather I/O). The type T is
    /// called a "header event", and describes the size of the trailing length
    /// data to be parsed by the reader (e.g., the `data` field of a TXN_LOG,
    /// or the `input` and `return` values of a TXN_CALL_FRAME)
    template <typename T, std::same_as<std::span<std::byte const>>... U>
        requires std::is_trivially_copyable_v<T>
    void record(
        std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
        T const &payload, U... bufs)
    {
        uint64_t seqno;
        uint8_t *payload_buf;
        size_t const payload_size = (size(bufs) + ... + sizeof payload);

        monad_event_descriptor *const event = monad_event_recorder_reserve(
            &exec_recorder_, payload_size, &seqno, &payload_buf);
        void *p = mempcpy(payload_buf, &payload, sizeof payload);
        ((p = mempcpy(p, data(bufs), size(bufs))), ...);
        event->event_type = std::to_underlying(type);
        event->user[MONAD_FLOW_BLOCK_SEQNO] = block_start_seqno_;
        event->user[MONAD_FLOW_TXN_ID] = opt_txn_num.value_or(-1) + 1;
        monad_event_recorder_commit(event, seqno);
    }

private:
    alignas(64) monad_event_recorder exec_recorder_;
    monad_event_ring exec_ring_;
    uint64_t block_start_seqno_;
    std::string ring_path_;
    int ring_fd_;
};

// Declare the global recorder object; this is initialized by the driver
// process if it wants execution event recording, and is left uninitialized to
// disable it (all internal functions check if it's `nullptr` before using it);
// we use a "straight" global variable rather than a "magic static" style
// singleton, because we don't care as much about preventing initialization
// races as we do about potential cost of poking at atomic guard variables
// every time
extern std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

/*
 * Helper free functions for execution event recording
 */

inline void record_exec_event(
    std::optional<uint32_t> opt_txn_num, monad_exec_event_type type)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        return e->record(opt_txn_num, type);
    }
}

template <typename T>
    requires std::is_trivially_copyable_v<T>
void record_exec_event(
    std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
    T const &payload)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        return e->record(opt_txn_num, type, payload);
    }
}

template <typename T, std::same_as<std::span<std::byte const>>... U>
    requires std::is_trivially_copyable_v<T>
void record_exec_event(
    std::optional<uint32_t> opt_txn_num, monad_exec_event_type type,
    T const &payload, U &&...bufs)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        return e->record(
            opt_txn_num, type, payload, std::forward<U...>(bufs...));
    }
}

MONAD_NAMESPACE_END
