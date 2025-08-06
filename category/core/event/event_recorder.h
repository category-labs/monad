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
 * Defines the event recorder object and its API; recorders are used for
 * writing events
 */

#include <stddef.h>
#include <stdint.h>

#include <category/core/event/event_ring.h>

struct monad_event_recorder;

#ifdef __cplusplus
extern "C"
{
#endif

/// Reserve resources to record an event; this returns an allocated event
/// descriptor with all fields populated except `seqno` and `event_type`.
/// It sets `payload` to the start of a payload buffer large enough to hold
/// `payload_size`. If `payload_size` is larger than UINT32_MAX, this returns
/// nullptr and sets *seqno == 0 and *payload == nullptr. When successful,
/// call monad_event_recorder_commit to finish recording.
static struct monad_event_descriptor *monad_event_recorder_reserve(
    struct monad_event_recorder *, size_t payload_size, uint64_t *seqno,
    uint8_t **payload);

/// Marks an event as ready, so that readers can observe it; this function is
/// called after populating all descriptor fields and copying the event
/// payload. The event descriptor and sequence number are the values returned
/// from an earlier call to monad_event_recorder_reserve
static void
monad_event_recorder_commit(struct monad_event_descriptor *, uint64_t seqno);

/// Take a timestamp, in nanoseconds since the UNIX epoch
static uint64_t monad_event_get_epoch_nanos();

struct monad_event_recorder
{
    struct monad_event_descriptor *descriptors;
    uint8_t *payload_buf;
    struct monad_event_ring_control *control;
    size_t desc_capacity_mask;
    size_t payload_buf_mask;
};

#ifdef __cplusplus
} // extern "C"
#endif

#define MONAD_EVENT_RECORDER_INTERNAL
#include "event_recorder_inline.h"
#undef MONAD_EVENT_RECORDER_INTERNAL
