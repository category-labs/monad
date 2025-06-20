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
 * This files defines a universal iterator that works for a variety of
 * different event sources: event rings, single EVENT_BUNDLE sections of
 * capture files, finalized block archives; this is similar in spirit to
 * the "event source" C API, but more powerful and using RAII resource
 * management
 */

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

#include <category/core/assert.h>
#include <category/core/event/evcap_reader.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_iter.h>
#include <category/core/event/event_source.h>

struct EventSourceSpec;

class BlockArchiveDirectory;
class EventCaptureFile;
class MappedEventRing;

// clang-format off

/// Generalization of `monad_evsrc_result` that also implements return codes
/// for --begin-seqno and --end-seqno range filtering command line options; the
/// return value of EventIterator::next
enum class EventIteratorResult : unsigned
{
    Success = MONAD_EVSRC_SUCCESS,     ///< Event produced and iterator advanced
    NotReady = MONAD_EVSRC_NOT_READY,  ///< No events ready yet (ring only)
    Gap = MONAD_EVSRC_GAP,             ///< Sequence gap (ring only)
    End = MONAD_EVSRC_END,             ///< Before beginning or past ending
    Error,                             ///< Error occurred
    Skipped,                           ///< Before --begin-seqno, but copied out
    AfterBegin,                        ///< First seen seqno > --begin-seqno
    AfterEnd                           ///< Saw a seqno > --end-seqno
};

// clang-format on

/// Common interface that generalizes both event ring and event capture
/// iterators
struct EventIterator
{
    EventIterator();
    EventIterator(EventIterator const &) = delete;
    EventIterator(EventIterator &&) noexcept;
    ~EventIterator();

    enum class Type : uint8_t
    {
        EventRing,
        EventCaptureSection,
        BlockArchive,
    };

    struct EventRingImpl
    {
        monad_event_ring_iter iter;
        MappedEventRing const *mapped_event_ring;
    };

    struct CaptureSectionImpl
    {
        monad_evcap_event_iter iter;
        EventCaptureFile const *capture_file;
        monad_evcap_event_section cur_section;
        std::optional<uint64_t> section_limit;
        uint64_t sections_consumed;

        std::optional<EventIteratorResult>
        try_load_next_section(EventIterator *);
    };

    struct BlockArchiveImpl
    {
        CaptureSectionImpl open_section;
        std::unique_ptr<EventCaptureFile> cur_capture_file;
        BlockArchiveDirectory const *archive_dir;
        EventSourceSpec const *source_spec;
        uint64_t blocks_consumed;

        std::optional<EventIteratorResult> try_load_next_block(EventIterator *);
    };

    Type iter_type;
    bool finished;
    monad_event_content_type content_type;

    union
    {
        EventRingImpl ring;
        CaptureSectionImpl evcap;
        BlockArchiveImpl archive;
    };

    std::optional<uint64_t> begin_seqno;
    std::optional<uint64_t> end_seqno;

    mutable int error_code;
    mutable char const *last_error_msg;

    /// Try to consume the next event in the stream and advance the iterator
    EventIteratorResult
    next(monad_event_descriptor *event, std::byte const **payload);

    /// Check if a payload is still valid (no-op for capture files)
    bool check_payload(monad_event_descriptor const *event) const;

    /// Return the last read sequence number
    uint64_t get_last_read_seqno() const;

    /// Return the last known sequence number (last written for event rings,
    /// last recorded for evcap files)
    uint64_t get_last_written_seqno() const;

    /// Clear an event gap (no-op for capture files)
    std::pair<uint64_t, uint64_t> clear_gap(bool can_recover);

    monad_evsrc_any const *get_evsrc_any() const;
};

inline EventIteratorResult
EventIterator::next(monad_event_descriptor *event, std::byte const **payload)
{
    if (finished) {
        return EventIteratorResult::End;
    }

    EventIteratorResult r;
    monad_event_descriptor const *mapped_event;

    // Get the next event descriptor and payload
    switch (iter_type) {
    case Type::EventRing:
        r = static_cast<EventIteratorResult>(
            monad_event_ring_iter_try_next(&ring.iter, event));
        if (r == EventIteratorResult::Success) [[likely]] {
            *payload = static_cast<std::byte const *>(
                monad_event_ring_payload_peek(ring.iter.event_ring, event));
        }
        break;

    case Type::EventCaptureSection:
    EventCaptureTryAgain:
        r = static_cast<EventIteratorResult>(monad_evcap_event_iter_next(
            &evcap.iter,
            &mapped_event,
            reinterpret_cast<void const **>(payload)));
        if (r == EventIteratorResult::Success) [[likely]] {
            *event = *mapped_event;
        }
        else {
            MONAD_DEBUG_ASSERT(r == EventIteratorResult::End);
            if (auto const load_result = evcap.try_load_next_section(this)) {
                finished = true;
                r = *load_result;
            }
            else {
                goto EventCaptureTryAgain;
            }
        }
        break;

    case Type::BlockArchive:
    BlockArchiveTryAgain:
        r = static_cast<EventIteratorResult>(monad_evcap_event_iter_next(
            &archive.open_section.iter,
            &mapped_event,
            reinterpret_cast<void const **>(payload)));
        if (r == EventIteratorResult::Success) [[likely]] {
            *event = *mapped_event;
        }
        else {
            MONAD_DEBUG_ASSERT(r == EventIteratorResult::End);
            if (auto const load_result = archive.try_load_next_block(this)) {
                finished = true;
                r = *load_result;
            }
            else {
                goto BlockArchiveTryAgain;
            }
        }
        break;

    default:
        MONAD_ABORT_PRINTF(
            "unknown source_type %hhu", std::to_underlying(iter_type));
    }

    if (r != EventIteratorResult::Success) {
        return r;
    }

    // In the success case, we do some post-processing for the common
    // begin-seqno, end-seqno options
    if (begin_seqno) {
        if (event->seqno < *begin_seqno) {
            // Too early, skip it
            // XXX: possibly remove this?
            return EventIteratorResult::Skipped;
        }
        bool const saw_begin = event->seqno == *begin_seqno;
        // Clear this so the comparison won't happen twice
        begin_seqno.reset();
        return saw_begin ? EventIteratorResult::Success
                         : EventIteratorResult::AfterBegin;
    }

    // Check if we've advanced to end_seqno (or past it, if we gapped or
    // started too late); if so we're done
    if (end_seqno) {
        if (event->seqno == *end_seqno) {
            finished = true;
            return EventIteratorResult::End;
        }
        if (event->seqno > *end_seqno) {
            finished = true;
            return EventIteratorResult::AfterEnd;
        }
    }

    return r;
}

inline bool
EventIterator::check_payload(monad_event_descriptor const *event) const
{
    return iter_type != Type::EventRing ||
           monad_event_ring_payload_check(ring.iter.event_ring, event);
}

inline uint64_t EventIterator::get_last_read_seqno() const
{
    switch (iter_type) {
    case Type::EventRing:
        return ring.iter.cur_seqno - 1;
    default:
        return 0; // TODO(ken): do something reasonable here
    }
}

inline uint64_t EventIterator::get_last_written_seqno() const
{
    switch (iter_type) {
    case Type::EventRing:
        return monad_event_ring_get_last_written_seqno(
            ring.iter.event_ring, false);
    case Type::EventCaptureSection:
        return evcap.iter.event_section->seqno_index.seqno_end;
    case Type::BlockArchive:
        return archive.open_section.cur_section.seqno_index.seqno_end;
    default:
        std::unreachable();
    }
}

inline std::pair<uint64_t, uint64_t> EventIterator::clear_gap(bool can_recover)
{
    if (iter_type == Type::EventRing) {
        auto const p = std::make_pair(
            ring.iter.cur_seqno, monad_event_ring_iter_reset(&ring.iter));
        finished = !can_recover;
        return p;
    }
    return {};
}

inline monad_evsrc_any const *EventIterator::get_evsrc_any() const
{
    switch (iter_type) {
    case Type::EventRing:
        return monad_evsrc_any_from(&ring.iter);
    case Type::EventCaptureSection:
        return monad_evsrc_any_from(&evcap.cur_section);
    case Type::BlockArchive:
        return monad_evsrc_any_from(&archive.open_section.cur_section);
    default:
        std::unreachable();
    }
}
