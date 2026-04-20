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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/event/event_recorder.h>
#include <category/core/event/event_recorder.hpp>
#include <category/core/event/event_ring.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <span>
#include <tuple>

#include <string.h>

MONAD_NAMESPACE_BEGIN

std::tuple<monad_event_descriptor *, std::byte *, uint64_t>
EventRecorder::setup_record_error_event(
    uint16_t event_type, monad_event_record_error_type error_type,
    size_t header_payload_size,
    std::span<std::span<std::byte const> const> trailing_payload_bufs,
    size_t original_payload_size)
{
    monad_event_record_error *error_payload;
    size_t error_payload_size;

    switch (error_type) {
    case MONAD_EVENT_RECORD_ERROR_OVERFLOW_4GB:
        [[fallthrough]];
    case MONAD_EVENT_RECORD_ERROR_OVERFLOW_EXPIRE:
        // When an event cannot be recorded due to its payload size, we still
        // record the first 8 KiB of that payload; it may help with diagnosing
        // the cause of the overflow, which is a condition that is not expected
        // in normal operation
        error_payload_size = RECORD_ERROR_TRUNCATED_SIZE;
        break;
    default:
        error_payload_size = sizeof *error_payload;
        break;
    }

    uint64_t seqno;
    uint8_t *payload_buf;
    monad_event_descriptor *const event = monad_event_recorder_reserve(
        &recorder_, error_payload_size, &seqno, &payload_buf);
    MONAD_ASSERT(event != nullptr, "non-overflow reservation must succeed");

    event->event_type = 1;
    error_payload = reinterpret_cast<monad_event_record_error *>(payload_buf);
    error_payload->error_type = error_type;
    error_payload->dropped_event_type = event_type;
    error_payload->requested_payload_size = original_payload_size;

    switch (error_type) {
    case MONAD_EVENT_RECORD_ERROR_OVERFLOW_4GB:
        [[fallthrough]];
    case MONAD_EVENT_RECORD_ERROR_OVERFLOW_EXPIRE: {
        // In these cases, the payload area is set up like this:
        //
        //   .----------------.-----------------------.---------------.
        //   | *error_payload | event header (type T) | truncated VLT |
        //   .----------------.-----------------------.---------------.
        //
        // The intention here is for the reader to be able to see some of
        // the event that was discarded; we never expect these errors to
        // happen, so recording as much information as possible may be
        // important for debugging how our assumptions were wrong.
        //
        // The event header is written by the call site: we pass a pointer
        // to it in the return value, and the caller writes to it as though
        // the recording did not fail. The code below is responsible for
        // writing the "variable-length trailing" (VLT) data, which is the
        // only part that is truncated; an earlier assertion ensures that
        // RECORD_ERROR_TRUNCATED_SIZE is large enough that the event
        // header is never truncated. We do include the event header's size
        // in the `error_payload->truncated_payload_size` field, however.
        error_payload->truncated_payload_size =
            RECORD_ERROR_TRUNCATED_SIZE - sizeof(*error_payload);
        size_t const truncated_vlt_offset =
            sizeof(*error_payload) + header_payload_size;
        size_t residual_size =
            RECORD_ERROR_TRUNCATED_SIZE - truncated_vlt_offset;
        void *p = payload_buf + truncated_vlt_offset;
        for (std::span<std::byte const> buf : trailing_payload_bufs) {
            size_t const copy_len = std::min(residual_size, size(buf));
            p = mempcpy(p, data(buf), copy_len);
            residual_size -= copy_len;
            if (residual_size == 0) {
                break;
            }
        }
    } break;

    default:
        error_payload->truncated_payload_size = 0;
        break;
    }

    return {
        event,
        reinterpret_cast<std::byte *>(payload_buf) + sizeof *error_payload,
        seqno};
}

MONAD_NAMESPACE_END
