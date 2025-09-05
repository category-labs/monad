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

#pragma once

/**
 * @file
 *
 * This file defines the execution event recorder, which is a global object.
 * It is up to the driver code using this library to configure it, otherwise
 * recording will remain disabled.
 */

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <limits>
#include <memory>
#include <span>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <utility>

#include <string.h>

MONAD_NAMESPACE_BEGIN

/// Event recording works in three steps: (1) reserving descriptor and payload
/// buffer space in the event ring, then (2) the user performs zero-copy
/// initialization of the payload directly in ring memory, then (3) the result
/// is committed to the event ring; this structure connects all three steps
template <typename T>
struct ReservedExecEvent
{
    monad_event_descriptor *event;
    T *payload;
    uint64_t seqno;
};

/// All execution event recording goes through this class; it owns the
/// `monad_event_recorder` object, the event ring memory mapping, and holds the
/// event ring's file descriptor open (so that the flock(2) remains in place);
/// it also keeps track of the block flow ID -- the sequence number of the
/// BLOCK_START event, copied into all subsequent block-level events
class ExecutionEventRecorder
{
public:
    explicit ExecutionEventRecorder(
        int ring_fd, std::string_view ring_path, monad_event_ring const &);

    ~ExecutionEventRecorder();

    /// Reserve resources to record a BLOCK_START event; also sets the
    /// current block flow ID
    [[nodiscard]] ReservedExecEvent<monad_exec_block_start>
    reserve_block_start_event();

    /// Reserve resources to record an event that occurs at block scope; T is
    /// the type of the "header" payload, and U... is a variadic sequence of
    /// trailing payload buffers of type `std::span<std::byte const>`, e.g.,
    /// TXN_LOG records the log header structure `struct monad_exec_txn_log`
    /// and two variadic byte sequences (for topics and log data)
    template <typename T, std::same_as<std::span<std::byte const>>... U>
    [[nodiscard]] ReservedExecEvent<T>
    reserve_block_event(monad_exec_event_type, U...);

    /// Reserve resources to record a transaction-level event
    template <typename T, std::same_as<std::span<std::byte const>>... U>
    [[nodiscard]] ReservedExecEvent<T> reserve_txn_event(
        monad_exec_event_type event_type, uint32_t txn_num,
        U &&...trailing_bufs)
    {
        auto r = reserve_block_event<T>(
            event_type, std::forward<U>(trailing_bufs)...);
        r.event->content_ext[MONAD_FLOW_TXN_ID] = txn_num + 1;
        return r;
    }

    /// Mark that the current block has ended
    void end_current_block();

    /// Commit the previously reserved event resources to the event ring
    template <typename T>
    void commit(ReservedExecEvent<T> const &);

    /// Record a block-level event with no payload in one step
    void record_block_marker_event(monad_exec_event_type);

    /// Record a transaction-level event with no payload in one step
    void record_txn_marker_event(monad_exec_event_type, uint32_t txn_num);

    monad_event_ring const *get_event_ring() const
    {
        return &exec_ring_;
    }

    static constexpr size_t RECORD_ERROR_TRUNCATED_SIZE = 1UL << 13;

private:
    /// Helper for creating a RECORD_ERROR event in place of the requested
    /// event, which could not be recorded
    std::tuple<monad_event_descriptor *, std::byte *, uint64_t>
    setup_record_error_event(
        monad_exec_event_type, monad_event_record_error_type,
        size_t header_payload_size,
        std::span<std::span<std::byte const> const> payload_bufs,
        size_t original_payload_size);

    alignas(64) monad_event_recorder exec_recorder_;
    monad_event_ring exec_ring_;
    uint64_t cur_block_start_seqno_;
    std::string ring_path_;
    int ring_fd_;
};

inline ReservedExecEvent<monad_exec_block_start>
ExecutionEventRecorder::reserve_block_start_event()
{
    ReservedExecEvent const block_start =
        reserve_block_event<monad_exec_block_start>(MONAD_EXEC_BLOCK_START);
    cur_block_start_seqno_ = block_start.seqno;
    block_start.event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = block_start.seqno;
    return block_start;
}

template <typename T, std::same_as<std::span<std::byte const>>... U>
ReservedExecEvent<T> ExecutionEventRecorder::reserve_block_event(
    monad_exec_event_type event_type, U... trailing_bufs)
{
    // This is checking that, in the event of a recorder error, we could still
    // fit the entire header event type T and the error reporting type in the
    // maximum "truncated buffer" size allocated to report errors
    static_assert(
        sizeof(T) + sizeof(monad_exec_record_error) <=
        RECORD_ERROR_TRUNCATED_SIZE);

    // This function does the following:
    //
    //   - Reserves an event descriptor
    //
    //   - Reserves payload buffer space to hold the event payload data type,
    //     which is a fixed-size, C-layout-compatible structure of type `T`;
    //     the caller will later initialize this memory, constructing their T
    //     instance within it
    //
    //   - Also reserves (as part of the above allocation) payload buffer space
    //     for variable-length arrays that follow the `T` object in the event
    //     payload. For example, the topics and log data arrays for TXN_LOG
    //     are variable-length data that is copied immediately following the
    //     main `T = monad_c_eth_txn_log` payload structure; in this kind of
    //     event, the payload type `monad_c_eth_txn_log` is called the "header"
    //
    // All variable-length trailing data segments are passed to this function
    // via the variadic list of arguments. They are treated as unstructured
    // data and have type `std::span<std::byte const>`. After payload space is
    // reserved for these byte arrays, they are also memcpy'd immediately.
    //
    // Events that do not have variable-length trailing data also use this
    // function, with an empty `U` parameter pack.
    //
    // The reason variable-length data is memcpy'd immediately but the fixed
    // sized part of the event payload (of type `T`) is not, is best explained
    // by example. Consider this C++ type that models an Ethereum log:
    //
    //    struct Log
    //    {
    //        byte_string data{};
    //        std::vector<bytes32_t> topics{};
    //        Address address{};
    //    }
    //
    // This type is not trivially copyable, but the underlying array elements
    // in the `data` and `topics` array can be trivially copied.
    //
    // The corresponding C-layout-compatible type describing the log,
    // `T = monad_c_eth_txn_log`, has to be manually initialized by the caller,
    // so this function returns a `monad_c_eth_txn_log *` pointing to the
    // payload buffer space for the caller to perform zero-copy initialization.
    //
    // We need to know the total size of the variable-length trailing data in
    // order to reserve enough space for it; since the caller always knows what
    // this data is, this function asks for the complete span rather than just
    // the size, and also does the memcpy now. This simplifies the recording
    // calls, and also the handling of the RECORD_ERROR type, which writes
    // diagnostic truncated payloads on overflow

    size_t const payload_size = (size(trailing_bufs) + ... + sizeof(T));
    if (payload_size > std::numeric_limits<uint32_t>::max()) [[unlikely]] {
        std::array<std::span<std::byte const>, sizeof...(trailing_bufs)> const
            trailing_bufs_array = {trailing_bufs...};
        auto const [event, header_buf, seqno] = setup_record_error_event(
            event_type,
            MONAD_EVENT_RECORD_ERROR_OVERFLOW_4GB,
            sizeof(T),
            trailing_bufs_array,
            payload_size);
        return {event, reinterpret_cast<T *>(header_buf), seqno};
    }
    if (payload_size >=
        exec_ring_.payload_buf_mask + 1 - 2 * MONAD_EVENT_WINDOW_INCR) {
        // The payload is smaller than the maximum possible size, but still
        // cannot fit entirely in the event ring's payload buffer. For example,
        // suppose we tried to allocate 300 MiB from a 256 MiB payload buffer.
        //
        // The event ring C API does not handle this as a special case;
        // instead, the payload buffer's normal ring buffer expiration logic
        // allows the allocation to "succeed" but it appears as expired
        // immediately upon allocation (for the expiration logic, see the
        // "Sliding window buffer" section of event_recorder.md).
        //
        // We treat this as a formal error so that the operator will know
        // to allocate a (much) larger event ring buffer.
        std::array<std::span<std::byte const>, sizeof...(trailing_bufs)> const
            trailing_bufs_array = {trailing_bufs...};
        auto const [event, header_buf, seqno] = setup_record_error_event(
            event_type,
            MONAD_EVENT_RECORD_ERROR_OVERFLOW_EXPIRE,
            sizeof(T),
            trailing_bufs_array,
            payload_size);
        return {event, reinterpret_cast<T *>(header_buf), seqno};
    }

    uint64_t seqno;
    uint8_t *payload_buf;
    monad_event_descriptor *const event = monad_event_recorder_reserve(
        &exec_recorder_, payload_size, &seqno, &payload_buf);
    MONAD_DEBUG_ASSERT(event != nullptr);
    if constexpr (sizeof...(trailing_bufs) > 0) {
        // Copy the variable-length trailing buffers; GCC issues a false
        // positive warning about this memcpy that must be disabled
#if !defined(__clang__)
    #pragma GCC diagnostic push
    #pragma GCC diagnostic ignored "-Wstringop-overflow"
    #pragma GCC diagnostic ignored "-Warray-bounds"
#endif
        void *p = payload_buf + sizeof(T);
        ((p = mempcpy(p, data(trailing_bufs), size(trailing_bufs))), ...);
#if !defined(__clang__)
    #pragma GCC diagnostic pop
#endif
    }
    event->event_type = event_type;
    event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = cur_block_start_seqno_;
    event->content_ext[MONAD_FLOW_TXN_ID] = 0;
    event->content_ext[MONAD_FLOW_ACCOUNT_INDEX] = 0;

    return {event, reinterpret_cast<T *>(payload_buf), seqno};
}

inline void ExecutionEventRecorder::end_current_block()
{
    cur_block_start_seqno_ = 0;
}

template <typename T>
void ExecutionEventRecorder::commit(ReservedExecEvent<T> const &exec_event)
{
    monad_event_recorder_commit(exec_event.event, exec_event.seqno);
}

inline void ExecutionEventRecorder::record_block_marker_event(
    monad_exec_event_type event_type)
{
    uint64_t seqno;
    uint8_t *payload_buf;
    monad_event_descriptor *const event =
        monad_event_recorder_reserve(&exec_recorder_, 0, &seqno, &payload_buf);
    event->event_type = std::to_underlying(event_type);
    event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = cur_block_start_seqno_;
    monad_event_recorder_commit(event, seqno);
}

inline void ExecutionEventRecorder::record_txn_marker_event(
    monad_exec_event_type event_type, uint32_t txn_num)
{
    uint64_t seqno;
    uint8_t *payload_buf;
    monad_event_descriptor *const event =
        monad_event_recorder_reserve(&exec_recorder_, 0, &seqno, &payload_buf);
    event->event_type = std::to_underlying(event_type);
    event->content_ext[MONAD_FLOW_BLOCK_SEQNO] = cur_block_start_seqno_;
    event->content_ext[MONAD_FLOW_TXN_ID] = txn_num + 1;
    monad_event_recorder_commit(event, seqno);
}

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

inline void record_block_marker_event(monad_exec_event_type event_type)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        e->record_block_marker_event(event_type);
    }
}

inline void
record_txn_marker_event(monad_exec_event_type event_type, uint32_t txn_num)
{
    if (auto *const e = g_exec_event_recorder.get()) {
        e->record_txn_marker_event(event_type, txn_num);
    }
}

MONAD_NAMESPACE_END
