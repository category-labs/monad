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

#include "iterator.hpp"
#include "command.hpp"
#include "file.hpp"

#include <cstdint>
#include <filesystem>
#include <memory>
#include <optional>

#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_reader.h>
#include <category/execution/ethereum/event/blockcap.h>

namespace fs = std::filesystem;

EventIterator::EventIterator()
    : iter_type{Type::EventRing}
    , finished{false}
    , ring{}
{
}

EventIterator::~EventIterator()
{
    switch (iter_type) {
    case Type::EventCaptureSection:
        monad_evcap_event_section_close(&evcap.cur_section);
        break;

    case Type::BlockArchive:
        monad_evcap_event_section_close(&archive.open_section.cur_section);
        archive.~BlockArchiveImpl();
        break;

    default:
        break;
    }
}

std::optional<EventIteratorResult>
EventIterator::CaptureSectionImpl::try_load_next_section(EventIterator *i)
{
    monad_evcap_section_desc const *const cur_event_sd = cur_section.event_sd;
    monad_evcap_event_section_close(&cur_section);
    ++sections_consumed;
    if (section_limit && sections_consumed == *section_limit) {
        return EventIteratorResult::End;
    }

    // XXX: this is not exactly the correct way to look through packed block
    // archives...
    // Look for the next event bundle section with the same schema type; if we
    // don't find one, the iteration ends
    monad_evcap_reader const *const evcap_reader = capture_file->get_reader();
    monad_evcap_section_desc const *const cur_schema_sd =
        monad_evcap_reader_load_linked_section_desc(
            evcap_reader, cur_event_sd->event_bundle.schema_desc_offset);
    monad_evcap_section_desc const *scan_event_sd = cur_event_sd;
    while (monad_evcap_reader_next_section(
        evcap_reader, MONAD_EVCAP_SECTION_EVENT_BUNDLE, &scan_event_sd)) {
        monad_evcap_section_desc const *const scan_schema_sd =
            monad_evcap_reader_load_linked_section_desc(
                evcap_reader, scan_event_sd->event_bundle.schema_desc_offset);
        // XXX: we either do a full comparison here (check all fields) or an
        // even shallower one (just check that the file offset is the same),
        // if we're going to guarantee that there is only one present
        if (scan_schema_sd->schema.content_type ==
            cur_schema_sd->schema.content_type) {
            break;
        }
    }

    if (scan_event_sd == nullptr) {
        // No matching event sections
        return EventIteratorResult::End;
    }
    i->error_code = monad_evcap_event_section_open(
        &cur_section, evcap_reader, scan_event_sd);
    if (i->error_code != 0) {
        i->last_error_msg = monad_evcap_reader_get_last_error();
        return EventIteratorResult::Error;
    }

    monad_evcap_event_section_open_iterator(&cur_section, &iter);
    return std::nullopt;
}

std::optional<EventIteratorResult>
EventIterator::BlockArchiveImpl::try_load_next_block(EventIterator *i)
{
    EventSourceQuery const &q = source_spec->source_query;
    uint64_t const cur_block_number =
        open_section.cur_section.event_sd->event_bundle.block_number;
    monad_evcap_event_section_close(&open_section.cur_section);
    ++blocks_consumed;
    if (q.count && blocks_consumed == *q.count) {
        return EventIteratorResult::End;
    }
    cur_capture_file.reset(); // Destroy the old capture file

    // Open the next block
    monad_evcap_reader *evcap_reader;
    int fd;
    char path_buf[64];
    i->error_code = monad_bcap_archive_open_block_reader(
        archive_dir->get_block_archive(),
        cur_block_number + 1,
        path_buf,
        sizeof path_buf,
        &fd,
        &evcap_reader,
        nullptr);
    if (i->error_code != 0) {
        i->last_error_msg = monad_bcap_get_last_error();
        return EventIteratorResult::Error;
    }
    auto const opt_resolved = lookup_capture_section(
        EventSourceFile::Type::BlockArchiveDirectory, evcap_reader, q);
    if (!opt_resolved) {
        i->last_error_msg = "no section in archive block";
        return EventIteratorResult::Error;
    }
    if (opt_resolved->resolved_sd->type != MONAD_EVCAP_SECTION_EVENT_BUNDLE) {
        i->last_error_msg =
            "resolved section in archive block has the wrong type";
        return EventIteratorResult::Error;
    }
    MONAD_ASSERT(opt_resolved->schema_sd != nullptr);
    if (opt_resolved->schema_sd->schema.content_type != i->content_type) {
        i->last_error_msg =
            "section query found different section in subsequent archive block";
        return EventIteratorResult::Error;
    }

    cur_capture_file = std::make_unique<EventCaptureFile>(
        archive_dir->get_origin_path() / fs::path{path_buf}, fd, evcap_reader);

    open_section.capture_file = cur_capture_file.get();
    open_section.section_limit = 1;
    i->error_code = monad_evcap_event_section_open(
        &open_section.cur_section, evcap_reader, opt_resolved->resolved_sd);
    if (i->error_code != 0) {
        i->last_error_msg = monad_evcap_reader_get_last_error();
        return EventIteratorResult::Error;
    }

    monad_evcap_event_section_open_iterator(
        &open_section.cur_section, &open_section.iter);
    return std::nullopt;
}
