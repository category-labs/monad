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
 * This file contains definitions that are shared between the event ring data
 * structure (event_ring.h) and the event capture library (evcap)
 */

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

// clang-format off

/// Describes what kind of event content is recorded in an event ring file;
/// different categories of events have different binary schemas, and this
/// identifies the integer namespace that the event descriptor's
/// `uint16_t event_type` field is drawn from
typedef enum monad_event_content_type : uint16_t
{
    MONAD_EVENT_CONTENT_TYPE_NONE,  ///< An invalid value
    MONAD_EVENT_CONTENT_TYPE_TEST,  ///< Used in simple automated tests
    MONAD_EVENT_CONTENT_TYPE_EXEC,  ///< Core execution events
    MONAD_EVENT_CONTENT_TYPE_COUNT  ///< Total number of content types
} monad_event_content_type_t;

/// Descriptor for an event; this fixed-size object describes the common
/// attributes of an event, and is broadcast to other threads via a shared
/// memory ring buffer (the threads are potentially in different processes).
/// The variably-sized extra content of the event (specific to each event type)
/// is called the "event payload"; it lives in a shared memory buffer called the
/// "payload buffer" which can be accessed using the info in this descriptor
struct monad_event_descriptor
{
    alignas(64) uint64_t seqno;  ///< Sequence number, for gap/liveness check
    uint16_t event_type;         ///< What kind of event this is
    uint16_t : 16;               ///< Unused tail padding
    uint32_t payload_size;       ///< Size of event payload
    uint64_t record_epoch_nanos; ///< Time event was recorded
    uint64_t payload_buf_offset; ///< Unwrapped offset of payload in p. buf
    uint64_t content_ext[4];     ///< Extensions for particular content types
};

// clang-format on

static_assert(sizeof(struct monad_event_descriptor) == 64);

/// Array of human-readable names for the event ring content types
extern char const
    *g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_COUNT];

#ifdef __cplusplus
} // extern "C"
#endif
