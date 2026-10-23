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
 * This file contains:
 *
 *   - Definitions of the event ring's shared memory structures
 *   - Functions which initialize and mmap event rings
 */

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <sys/types.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_event_descriptor;
struct monad_event_recorder;
struct monad_event_ring_header;
struct monad_event_ring_iter;

enum monad_event_content_type : uint16_t;
enum monad_event_record_error_type : uint16_t;

typedef enum monad_event_content_type monad_event_content_type_t;

// clang-format off

/// Describes a shared memory event ring that has been mapped into the address
/// space of the current process
struct monad_event_ring
{
    int mmap_prot;                              ///< Our pages mmap'ed with this
    struct monad_event_ring_header *header;     ///< Event ring metadata
    struct monad_event_descriptor *descriptors; ///< Event descriptor ring array
    uint8_t *payload_buf;                       ///< Payload buffer base address
    void *context_area;                         ///< Ring-specific storage
    uint64_t desc_capacity_mask;                ///< Descriptor capacity - 1
    uint64_t payload_buf_mask;                  ///< Payload buffer size - 1
};

/// Describes the size of an event ring's primary data structures
struct monad_event_ring_size
{
    size_t descriptor_capacity; ///< # entries in event descriptor array
    size_t payload_buf_size;    ///< Byte size of payload buffer
    size_t context_area_size;   ///< Byte size of context area section
};

/// Control registers of the event ring; resource allocation within an event
/// ring, i.e., the reserving of an event descriptor slot and payload buffer
/// space to record an event, is tracked using this object
struct monad_event_ring_control
{
    alignas(64) uint64_t last_seqno; ///< Last seq. number allocated by writer
    uint64_t next_payload_byte;      ///< Next payload buffer byte to allocate
    alignas(64) uint64_t buffer_window_start; ///< See event_recorder.md docs
};

/// Event ring shared memory files start with this header structure
struct monad_event_ring_header
{
    char magic[6];                           ///< 'RINGvv', vv = version number
    monad_event_content_type_t content_type; ///< Kind of events in this ring
    uint8_t schema_hash[32];                 ///< Ensure event definitions match
    struct monad_event_ring_size size;       ///< Size of following structures
    struct monad_event_ring_control control; ///< Tracks ring's state/status
};

/// Result of trying to read an event descriptor from an event ring
typedef enum monad_event_ring_result : uint16_t
{
    MONAD_EVENT_RING_SUCCESS = 0,        ///< Event descriptor read successfully
    MONAD_EVENT_RING_NOT_READY = 0x0100, ///< No event descriptor available yet
    MONAD_EVENT_RING_GAP = 0x0101,       ///< Sequence number gap detected
} monad_event_ring_result_t;

// clang-format on

/// Return an initialized event ring size structure, after performing checks
/// on valid size limits; a "shift" is the power-of-2 exponent for a size
int monad_event_ring_init_size(
    uint8_t descriptors_shift, uint8_t payload_buf_shift,
    uint16_t context_large_pages, struct monad_event_ring_size *);

/// Given the size parameters of an event ring, return the total number of
/// bytes needed to store it in memory; can be used to ftruncate(2) a file
/// range large enough to store an event ring
size_t monad_event_ring_calc_storage(struct monad_event_ring_size const *);

/// Initializes an event ring "shared file", to be mmap'ed by multiple
/// processes later. Given an open file descriptor, this creates the event
/// ring data structures at the given offset within that file
int monad_event_ring_init_file(
    struct monad_event_ring_size const *, monad_event_content_type_t,
    uint8_t const (*schema_hash)[32], int ring_fd, off_t ring_offset,
    char const *error_name);

/// Given an open file descriptor which contains an initialized event ring at
/// `ring_offset`, mmap the event ring into our address space; mmap_extra_flags
/// is OR'ed with MAP_SHARED to produce the final flags
int monad_event_ring_mmap(
    struct monad_event_ring *, int mmap_prot, int mmap_extra_flags, int ring_fd,
    off_t ring_offset, char const *error_name);

/// Remove an event ring's shared memory mappings from our process' address
/// space
void monad_event_ring_unmap(struct monad_event_ring *);

/// Try to copy the event descriptor corresponding to a particular sequence
/// number; returns MONAD_EVENT_RING_SUCCESS only if the descriptor was
/// available and its contents were copied into the output descriptor buffer
static monad_event_ring_result_t monad_event_ring_try_copy(
    struct monad_event_ring const *, uint64_t seqno,
    struct monad_event_descriptor *);

/// Obtain a pointer to the event's payload in shared memory in a zero-copy
/// fashion; to check for expiration, call monad_event_payload_check
static void const *monad_event_ring_payload_peek(
    struct monad_event_ring const *, struct monad_event_descriptor const *);

/// Return true if the zero-copy buffer returned by monad_event_payload_peek
/// still contains the event payload for the given descriptor; returns false if
/// the event payload has been overwritten
static bool monad_event_ring_payload_check(
    struct monad_event_ring const *, struct monad_event_descriptor const *);

/// Copy the event payload from shared memory into the supplied buffer, up to
/// `n` bytes; returns nullptr if the event payload has been overwritten
static void *monad_event_ring_payload_memcpy(
    struct monad_event_ring const *, struct monad_event_descriptor const *,
    void *dst, size_t n);

/// Return the sequence number of the last event that was written to the event
/// ring; if sync_wait is true, wait until the event is fully written before
/// returning (i.e., prevent us from seeing partial writes)
static uint64_t monad_event_ring_get_last_written_seqno(
    struct monad_event_ring const *, bool sync_wait);

/// Initialize an iterator to point to the most recently produced event in the
/// event ring
int monad_event_ring_init_iterator(
    struct monad_event_ring const *, struct monad_event_ring_iter *);

/// Initialize a recorder to write into an event ring
int monad_event_ring_init_recorder(
    struct monad_event_ring const *, struct monad_event_recorder *);

/// Return a description of the last error that occurred on this thread
char const *monad_event_ring_get_last_error();

/// This should be changed whenever anything binary-affecting in this file
/// changes (e.g., any structure or enumeration value that is shared memory
/// resident, e.g., `enum monad_event_content_type`)
constexpr uint8_t MONAD_EVENT_RING_HEADER_VERSION[] = {
    'R', 'I', 'N', 'G', '0', '1'};

/*
 * Event ring size limits
 */

constexpr uint8_t MONAD_EVENT_MIN_DESCRIPTORS_SHIFT = 16;
constexpr uint8_t MONAD_EVENT_MAX_DESCRIPTORS_SHIFT = 32;

constexpr uint8_t MONAD_EVENT_MIN_PAYLOAD_BUF_SHIFT = 27;
constexpr uint8_t MONAD_EVENT_MAX_PAYLOAD_BUF_SHIFT = 40;

/// Sliding window increment, see `event_recorder.md` documentation
constexpr uint64_t MONAD_EVENT_WINDOW_INCR = 1UL << 24;

/// Allocations from an event ring payload buffer have this alignment
constexpr size_t MONAD_EVENT_PAYLOAD_ALIGN = 16;

/*
 * Record error event payload definitions
 */

// clang-format off

// In the schema of every content type, the event_type with code 1 is always a
// `RECORD_ERROR` which indicates a payload of `struct monad_event_record_error`
constexpr uint16_t MONAD_EVENT_RECORD_ERROR_EVENT_TYPE = 1;

struct monad_event_record_error
{
    alignas(16) enum monad_event_record_error_type
        error_type;                  ///< Kind of recording error that occurred
    uint16_t dropped_event_type;     ///< What kind of event was discarded
    uint32_t truncated_payload_size; ///< Size of truncated trailing payload
    uint64_t requested_payload_size; ///< Untruncated size of event payload
};

enum monad_event_record_error_type : uint16_t
{
    MONAD_EVENT_RECORD_ERROR_NONE,            ///< No error
    MONAD_EVENT_RECORD_ERROR_OVERFLOW_4GB,    ///< Payload overflows UINT32_MAX
    MONAD_EVENT_RECORD_ERROR_OVERFLOW_EXPIRE, ///< Payload expired on creation
    MONAD_EVENT_RECORD_ERROR_MISSING_EVENT,   ///< Missing expected from peer
};

// clang-format on

#ifdef __cplusplus
} // extern "C"
#endif

#define MONAD_EVENT_RING_INTERNAL
#include "event_ring_inline.h"
#undef MONAD_EVENT_RING_INTERNAL
