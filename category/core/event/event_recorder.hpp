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
 * This file defines a C++ interface for recording to event rings
 */

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <span>
#include <tuple>
#include <type_traits>
#include <utility>

#include <string.h>

MONAD_NAMESPACE_BEGIN

/// C++ event recording works in three steps: (1) reserving descriptor and
/// payload buffer space in an event ring, then (2) the user performs zero-copy
/// typed initialization of the payload directly in ring memory, then (3) the
/// result is committed to the event ring; this type connects all three steps
template <typename T>
struct ReservedEvent
{
    monad_event_descriptor *event;
    T *payload;
    uint64_t seqno;
};

/// An interface to an event recorder that represents "reserve" and "commit"
/// semantics as the ReservedEvent<T> template type, and has convenient support
/// for capturing recording errors
class EventRecorder
{
public:
    explicit EventRecorder(monad_event_recorder const &recorder) noexcept
        : recorder_{recorder}
    {
    }

    /// Reserve resources to record an event; T is the type of the "header"
    /// payload, and U... is a variadic sequence of trailing payload buffers
    /// of type `std::span<std::byte const>`, e.g., TXN_LOG records the log
    /// header structure `struct monad_exec_txn_log` and two variadic byte
    /// sequences (for topics and log data)
    template <
        typename T, typename EventEnum,
        std::same_as<std::span<std::byte const>>... U>
        requires std::is_enum_v<EventEnum>
    [[nodiscard]] ReservedEvent<T> reserve_event(EventEnum, U...);

    /// Commit the previously reserved event resources to the event ring
    template <typename T>
    void commit(ReservedEvent<T> const &);

    static constexpr size_t RECORD_ERROR_TRUNCATED_SIZE = 1UL << 13;

protected:
    alignas(64) monad_event_recorder recorder_;

    /// Helper for creating a RECORD_ERROR event in place of the requested
    /// event, which could not be recorded
    std::tuple<monad_event_descriptor *, std::byte *, uint64_t>
    setup_record_error_event(
        uint16_t event_type, monad_event_record_error_type,
        size_t header_payload_size,
        std::span<std::span<std::byte const> const> payload_bufs,
        size_t original_payload_size);
};

template <
    typename T, typename EventEnum,
    std::same_as<std::span<std::byte const>>... U>
    requires std::is_enum_v<EventEnum>
ReservedEvent<T>
EventRecorder::reserve_event(EventEnum event_type, U... trailing_bufs)
{
    // This is checking that, in the event of a recorder error, we could still
    // fit the entire header event type T and the error reporting type in the
    // maximum "truncated buffer" size allocated to report errors
    static_assert(
        sizeof(T) + sizeof(monad_event_record_error) <=
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
            std::to_underlying(event_type),
            MONAD_EVENT_RECORD_ERROR_OVERFLOW_4GB,
            sizeof(T),
            trailing_bufs_array,
            payload_size);
        return {event, reinterpret_cast<T *>(header_buf), seqno};
    }
    if (payload_size >=
        recorder_.payload_buf_mask + 1 - 2 * MONAD_EVENT_WINDOW_INCR) {
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
            std::to_underlying(event_type),
            MONAD_EVENT_RECORD_ERROR_OVERFLOW_EXPIRE,
            sizeof(T),
            trailing_bufs_array,
            payload_size);
        return {event, reinterpret_cast<T *>(header_buf), seqno};
    }

    uint64_t seqno;
    uint8_t *payload_buf;
    monad_event_descriptor *const event = monad_event_recorder_reserve(
        &recorder_, payload_size, &seqno, &payload_buf);
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
    event->event_type = std::to_underlying(event_type);
    return {event, reinterpret_cast<T *>(payload_buf), seqno};
}

template <typename T>
void EventRecorder::commit(ReservedEvent<T> const &r)
{
    monad_event_recorder_commit(r.event, r.seqno);
}

MONAD_NAMESPACE_END
