// Copyright (C) 2025-26 Category Labs, Inc.
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
 * This file defines a C++ interface for recording to event rings. See the
 * documentation in `event_recorder.md` for details.
 */

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_ring.h>
#include <category/core/likely.h>
#include <category/core/mem/align.h>

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <expected>
#include <limits>
#include <memory>
#include <span>
#include <system_error>
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
    static std::expected<std::unique_ptr<EventRecorder>, std::errc>
    from_event_ring(monad_event_ring const *const ring)
    {
        auto t = std::make_unique<EventRecorder>();
        if (int const r = monad_event_ring_init_recorder(ring, &t->recorder_)) {
            return std::unexpected(std::errc{r});
        }
        return t;
    }

    /// Reserve resources to record an event; T is the type of the "core" event
    /// payload, and U... is a variadic sequence of trailing payload buffers
    /// of type `std::span<std::byte const>`, for variable-length trailing
    /// arrays (see the documentation for an explanation)
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

    friend constexpr std::unique_ptr<EventRecorder>
    std::make_unique<EventRecorder>();

    EventRecorder() noexcept = default;
};

template <
    typename T, typename EventEnum,
    std::same_as<std::span<std::byte const>>... U>
    requires std::is_enum_v<EventEnum>
ReservedEvent<T>
EventRecorder::reserve_event(EventEnum const event_type, U... trailing_bufs)
{
    static_assert(
        alignof(T) <= MONAD_EVENT_PAYLOAD_ALIGN,
        "Payload type `T` requires greater alignment than payload buffer "
        "allocator guarantees");

    // This is checking that, in the event of a recorder error, we could still
    // fit the entire header event type T and the error reporting type in the
    // maximum "truncated buffer" size allocated to report errors
    static_assert(
        sizeof(T) + sizeof(monad_event_record_error) <=
        RECORD_ERROR_TRUNCATED_SIZE);

    // In the event of a recording error, we'll record the `T` instance at
    // the next address after a `struct monad_event_record_error` object;
    // this ensures we won't under-align the `T{}`
    static_assert(alignof(monad_event_record_error) >= alignof(T));

    // payload_size is the true size requested, and alloc_payload_size is the
    // aligned size actually allocated from the event ring. The former is
    // recorded in the event descriptor, but the latter must be used for the
    // various size overflow checks.
    size_t const payload_size = (size(trailing_bufs) + ... + sizeof(T));
    size_t const alloc_payload_size =
        monad_round_size_to_align(payload_size, MONAD_EVENT_PAYLOAD_ALIGN);
    if (MONAD_UNLIKELY(
            alloc_payload_size > std::numeric_limits<uint32_t>::max())) {
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
    if (MONAD_UNLIKELY(
            alloc_payload_size >=
            recorder_.payload_buf_mask + 1 - 2 * MONAD_EVENT_WINDOW_INCR)) {
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
    MONAD_ASSERT(
        event != nullptr,
        "nullptr only when payload_size > UINT32_MAX, but handled above?");
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
