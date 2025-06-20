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

#include "file.hpp"
#include "command.hpp"
#include "err_cxx.hpp"
#include "iterator.hpp"
#include "util.hpp"

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <format>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <sys/file.h>
#include <sysexits.h>
#include <unistd.h>

#include <category/core/assert.h>
#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_reader.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_iter.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/event/event_source.h>
#include <category/execution/ethereum/event/blockcap.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_iter_help.h>

namespace fs = std::filesystem;

template <>
struct std::formatter<monad_event_flock_info> : std::formatter<std::string_view>
{
    template <class FmtContext>
    FmtContext::iterator
    format(monad_event_flock_info &i, FmtContext &ctx) const
    {
        std::string const s =
            std::format("{} [{:c}]", i.pid, i.lock == LOCK_EX ? 'W' : 'R');
        return this->std::formatter<std::string_view>::format(
            std::string_view{s}, ctx);
    }
};

namespace
{

std::string validate_consensus_event_param(
    EventSourceSpec const &source_spec, monad_event_content_type_t content_type)
{
    EventSourceQuery const &q = source_spec.source_query;
    if (q.consensus_event && content_type != MONAD_EVENT_CONTENT_TYPE_EXEC) {
        return std::format(
            "event source {} has a consensus event seek point, but content "
            "type is {} [{}], not the required {} [{}]",
            source_spec.describe(),
            g_monad_event_content_type_names[content_type],
            std::to_underlying(content_type),
            g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_EXEC],
            std::to_underlying(MONAD_EVENT_CONTENT_TYPE_EXEC));
    }
    return {};
}

std::optional<ResolvedCaptureSections> lookup_capture_section_with_block(
    monad_evcap_reader const *evcap_reader, EventSourceQuery const &q)
{
    using enum CaptureSectionSpec::SeekOrigin;

    monad_evcap_section_desc const *scan_sd = nullptr;
    monad_evcap_section_desc const *schema_sd;

    CaptureSectionSpec const &css = q.section.value_or(CaptureSectionSpec{
        .origin = SectionType,
        .section_type = MONAD_EVCAP_SECTION_EVENT_BUNDLE});

    MONAD_ASSERT(q.block->type == BlockLabel::Type::BlockNumber);
    while (monad_evcap_reader_next_section(
        evcap_reader, MONAD_EVCAP_SECTION_EVENT_BUNDLE, &scan_sd)) {
        if (scan_sd->event_bundle.block_number != q.block->block_number) {
            continue;
        }
        schema_sd = monad_evcap_reader_load_linked_section_desc(
            evcap_reader, scan_sd->event_bundle.schema_desc_offset);
        switch (css.origin) {
        case SectionType:
            return ResolvedCaptureSections{scan_sd, schema_sd};
        case ContentType:
            if (schema_sd->schema.content_type == css.content_type) {
                return ResolvedCaptureSections{scan_sd, schema_sd};
            }
            break;
        default:
            std::unreachable();
        }
    }

    return std::nullopt;
}

#if 0
size_t count_subsequent_sections(
    monad_evcap_reader const *evcap_reader, monad_evcap_section_desc const *event_sd, std::optional<monad_event_content_type_t> content_type)
{
    size_t count = 0;
    while (monad_evcap_reader_next_section(
            evcap_reader, MONAD_EVCAP_SECTION_EVENT_BUNDLE, &event_sd)) {
        monad_evcap_section_desc const *const schema_sd =
            monad_evcap_reader_load_linked_section_desc(
                    evcap_reader, event_sd->event_bundle.schema_desc_offset);
        monad_event_content_type_t const section_content_type =
                schema_sd->schema.content_type;
        if (!content_type || *content_type == section_content_type) {
            ++count;
        }
    }
    return count;
}

// This function is used both for EventCaptureFile and to validate the first
// block in a BlockArchiveDirectory
std::string validate_capture_file_source_spec(EventSourceSpec const &source_spec, monad_evcap_reader const *evcap_reader)
{
    EventSourceQuery const &q = source_spec.source_query;
    auto const ex_opt_resolved =
        lookup_capture_section(source_spec.source_file->get_type(), evcap_reader, q);
    if (!ex_opt_resolved) {
        return std::move(ex_opt_resolved).error();
    }
    if (!*ex_opt_resolved) {
        if (q.content_type || q.section_number || q.block_label) {
            return std::format("no section matches query parameters in {}", source_spec.describe());
        }
        else {
            // No EVENT_BUNDLE sections present; empty capture files are not
            // a validation error
            return {};
        }
    }
    ResolvedCaptureSections const &sections = **ex_opt_resolved;

    // There is a single section if
    //
    //   1. They didn't specify a section, and there is only one event
    //      section OR
    //   2. They did explicitly ask for one section, regardless
    //      of how many there are
    size_t const actual_section_count =
            1 + count_subsequent_sections(ecr, sections.event_sd, q.content_type.value_or(MONAD_EVENT_CONTENT_TYPE_NONE));
    bool const is_single_section =
            (!source_spec.opt_capture_spec && actual_section_count == 1) ||
            (q.count && *q.count == 1);

    if (!is_single_section && source_spec.opt_capture_spec &&
        source_spec.opt_capture_spec->count &&
        actual_section_count < *source_spec.opt_capture_spec->count) {
        return std::format(
                "capture spec requests {} sections, but only {} are "
                "available",
                *source_spec.opt_capture_spec->count,
                actual_section_count);
    }

    // Static sequence number checks
    bool const has_seqno_bounds =
            source_spec.opt_begin_seqno || source_spec.opt_end_seqno;
    if (has_seqno_bounds && !is_single_section) {
        return std::format("--begin-seqno/--end-seqno cannot be specified on "
                           "multi-section iteration");
    }
    if (has_seqno_bounds) {
        // XXX: degrade to scanning instead of outright failure?
        if (sections.event_sd->event_bundle.seqno_index_desc_offset != 0) {
            return std::format("--begin-seqno/--end-seqno specified but bundle "
                               "has no seqno index");
        }

        if (std::string const s = validate_consensus_event_param(source_spec); !std::empty(s)) {
            return s;
        }

        uint64_t const section_begin_seqno =
                sections.event_sd->event_bundle.start_seqno;
        uint64_t const section_end_seqno =
                section_begin_seqno + sections.event_sd->event_bundle.event_count;
        if (source_spec.opt_begin_seqno &&
            *source_spec.opt_begin_seqno < section_begin_seqno) {
            return std::format(
                    "--begin-seqno {} is before first sequence number {}",
                    *source_spec.opt_begin_seqno,
                    section_begin_seqno);
        }
        if (source_spec.opt_end_seqno &&
            *source_spec.opt_end_seqno > section_end_seqno) {
            return std::format(
                    "--end-seqno {} is after last sequence number {}",
                    *source_spec.opt_end_seqno,
                    section_end_seqno);
        }
    }
    return {};
}
#endif

} // End of anonymous namespace

std::string CaptureSectionSpec::describe() const
{
    char const *origin_name = nullptr;
    switch (origin) {
    case SeekOrigin::Unspecified:
        origin_name = "?";
        break;
    case SeekOrigin::Absolute:
        origin_name = "abs";
        break;
    case SeekOrigin::SectionType:
        origin_name = g_monad_evcap_section_names[section_type];
        break;
    case SeekOrigin::ContentType:
        origin_name = g_monad_event_content_type_names[content_type];
        break;
    }
    if (offset) {
        return std::format("{}.{}", origin_name, *offset);
    }
    return std::format("{}.<none>", origin_name);
}

std::string EventSourceQuery::describe() const
{
    std::vector<std::string> descriptions;
    if (section) {
        descriptions.emplace_back(
            std::format("section={}", section->describe()));
    }
    if (block) {
        descriptions.emplace_back(std::format("block={}", *block));
    }
    if (count) {
        descriptions.emplace_back(std::format("count={}", *count));
    }
    if (consensus_event) {
        descriptions.emplace_back(std::format(
            "exec_event={}",
            g_monad_exec_event_metadata[*consensus_event].c_name));
    }
    return descriptions.empty() ? "" : std::format("{}", descriptions);
}

std::string EventSourceSpec::describe() const
{
    return source_file->describe() + source_query.describe();
}

std::string EventSourceSpec::init_iterator(EventIterator *iter) const
{
    return source_file->init_iterator(iter, *this);
}

MappedEventRing::MappedEventRing(MappedEventRing &&other) noexcept
    : origin_path_{std::move(other.origin_path_)}
    , ring_fd_{other.ring_fd_}
    , initial_liveness_{other.initial_liveness_}
    , force_live_{other.force_live_}
    , event_ring_{other.event_ring_}
{
    other.ring_fd_ = -1;
    other.event_ring_ = {};
}

MappedEventRing::~MappedEventRing()
{
    (void)close(ring_fd_);
    monad_event_ring_unmap(&event_ring_);
}

std::string MappedEventRing::describe() const
{
    constexpr size_t MAX_FLOCKS = 128;

    EventRingLiveness current_liveness = initial_liveness_;
    std::string live_suffix;
    if (current_liveness == EventRingLiveness::Live) {
        monad_event_flock_info flocks[MAX_FLOCKS];
        size_t lock_count = std::size(flocks);
        if (int const rc =
                monad_event_ring_query_flocks(ring_fd_, flocks, &lock_count)) {
            live_suffix = std::format(", pids not available {}", rc);
        }
        else if (lock_count == 1) {
            live_suffix = std::format(", {}", flocks[0]);
        }
        else if (lock_count == 0) {
            current_liveness = EventRingLiveness::Abandoned;
        }
        else {
            live_suffix = std::format(", {}", std::span{flocks, lock_count});
        }
    }
    if (force_live_) {
        live_suffix += ", forced live";
    }
    return std::format(
        "{} [{}{}]",
        origin_path_.string(),
        ::describe(current_liveness),
        live_suffix);
}

bool MappedEventRing::is_finalized() const
{
    if (force_live_) {
        return false;
    }
    switch (initial_liveness_) {
    case EventRingLiveness::Live:
        return event_ring_is_abandoned(ring_fd_);
    case EventRingLiveness::Abandoned:
        [[fallthrough]];
    case EventRingLiveness::Snapshot:
        return true;
    default:
        std::unreachable();
    }
}

std::string MappedEventRing::validate(EventSourceSpec const &source_spec) const
{
    EventSourceQuery const &q = source_spec.source_query;
    if (q.section) {
        return std::format(
            "event ring file `{}` cannot have a capture section", describe());
    }
    if (q.block && !q.consensus_event) {
        return std::format(
            "event ring file `{}` specifies block label {}, but no 'exec' seek "
            "origin specified",
            describe(),
            *q.block);
    }
    if (std::string s = validate_consensus_event_param(
            source_spec, get_header()->content_type);
        !s.empty()) {
        return s;
    }
    return {};
}

std::string MappedEventRing::init_iterator(
    EventIterator *iter, EventSourceSpec const &source_spec) const
{
    monad_event_ring_header const *const header = get_header();
    monad_event_ring_iter &ring_iter = iter->ring.iter;
    iter->ring.mapped_event_ring = this;
    iter->iter_type = EventIterator::Type::EventRing;
    iter->finished = false;
    iter->content_type = header->content_type;
    iter->error_code = 0;
    iter->last_error_msg = nullptr;

    if (monad_event_ring_init_iterator(&event_ring_, &ring_iter) != 0) {
        return monad_event_ring_get_last_error();
    }

    if (source_spec.opt_begin_seqno) {
        iter->begin_seqno =
            monad_evsrc_iter_set_seqno(
                &ring_iter, *source_spec.opt_begin_seqno) == MONAD_EVSRC_SUCCESS
                ? source_spec.opt_begin_seqno
                : std::nullopt;
    }
    else if (initial_liveness_ == EventRingLiveness::Abandoned) {
        // Abandoned ring and no --begin-seqno parameter; start as
        // far back as possible
        size_t const desc_capacity = header->size.descriptor_capacity;
        uint64_t const last_seqno = monad_event_ring_get_last_written_seqno(
            &event_ring_, /*sync_wait=*/false);
        if (last_seqno <= desc_capacity) {
            monad_event_ring_iter_set_seqno(&ring_iter, 1);
        }
        else {
            monad_event_ring_iter_set_seqno(
                &ring_iter, last_seqno + 1 - desc_capacity);
        }
    }
    else if (initial_liveness_ == EventRingLiveness::Snapshot) {
        // Snapshot ring without --begin-seqno parameter; start at 1
        monad_event_ring_iter_set_seqno(&ring_iter, 1);
    }
    iter->end_seqno = source_spec.opt_end_seqno;
    return {};
}

EventCaptureFile::EventCaptureFile(EventCaptureFile &&other) noexcept
    : origin_path_{std::move(other.origin_path_)}
    , evcap_fd_{other.evcap_fd_}
    , evcap_reader_{other.evcap_reader_}
{
    other.evcap_fd_ = -1;
    other.evcap_reader_ = nullptr;
}

EventCaptureFile::~EventCaptureFile()
{
    (void)close(evcap_fd_);
    monad_evcap_reader_destroy(evcap_reader_);
}

std::string EventCaptureFile::describe() const
{
    return std::format("{} [capture]", origin_path_.string());
}

std::string EventCaptureFile::validate(EventSourceSpec const &source_spec) const
{
    EventSourceQuery const &q = source_spec.source_query;

    if (q.block && q.section) {
        if (q.section->offset) {
            return "cannot specify 'block' parameter with any 'section' "
                   "parameter containing an explict offset";
        }
        if (q.section->origin == CaptureSectionSpec::SeekOrigin::Absolute) {
            return "cannot specify 'block' parameter with an absolute "
                   "'section'";
        }
    }

    auto const opt_resolved =
        lookup_capture_section(get_type(), evcap_reader_, q);
    monad_event_content_type_t const content_type =
        opt_resolved && opt_resolved->schema_sd != nullptr
            ? opt_resolved->schema_sd->schema.content_type
            : MONAD_EVENT_CONTENT_TYPE_NONE;

    return validate_consensus_event_param(source_spec, content_type);
}

std::string EventCaptureFile::init_iterator(
    EventIterator *iter, EventSourceSpec const &source_spec) const
{
    auto const opt_resolved = lookup_capture_section(
        get_type(), evcap_reader_, source_spec.source_query);

    iter->iter_type = EventIterator::Type::EventCaptureSection;
    iter->content_type = opt_resolved && opt_resolved->schema_sd != nullptr
                             ? opt_resolved->schema_sd->schema.content_type
                             : MONAD_EVENT_CONTENT_TYPE_NONE;
    iter->error_code = 0;
    iter->last_error_msg = nullptr;
    if (iter->content_type == MONAD_EVENT_CONTENT_TYPE_NONE) {
        // Empty capture file case
        iter->finished = true;
        return {};
    }
    iter->finished = false;

    ResolvedCaptureSections const &sections = *opt_resolved;
    iter->content_type = sections.schema_sd->schema.content_type;
    iter->evcap.capture_file = this;
    iter->evcap.section_limit = source_spec.source_query.count;
    iter->evcap.sections_consumed = 0;

    if (monad_evcap_event_section_open(
            &iter->evcap.cur_section, evcap_reader_, sections.resolved_sd) !=
        0) {
        return std::format(
            "evcap library error opening iterator to section {} -- {}",
            sections.resolved_sd->index,
            monad_evcap_reader_get_last_error());
    }

    monad_evcap_event_section_open_iterator(
        &iter->evcap.cur_section, &iter->evcap.iter);
    if (source_spec.opt_begin_seqno) {
        iter->begin_seqno =
            monad_evsrc_iter_set_seqno(
                &iter->evcap.iter, *source_spec.opt_begin_seqno) ==
                    MONAD_EVSRC_SUCCESS
                ? source_spec.opt_begin_seqno
                : std::nullopt;
    }
    if (source_spec.opt_end_seqno) {
        monad_evcap_event_iter dummy_iter;
        monad_evcap_event_section_open_iterator(
            &iter->evcap.cur_section, &dummy_iter);
        iter->end_seqno =
            monad_evsrc_iter_set_seqno(
                &dummy_iter, *source_spec.opt_end_seqno) == MONAD_EVSRC_SUCCESS
                ? source_spec.opt_end_seqno
                : std::nullopt;
    }
    return {};
}

BlockArchiveDirectory::BlockArchiveDirectory(
    BlockArchiveDirectory &&other) noexcept
    : origin_path_{std::move(other.origin_path_)}
    , archive_fd_{other.archive_fd_}
    , archive_{other.archive_}
{
    other.archive_fd_ = -1;
    other.archive_ = nullptr;
}

BlockArchiveDirectory::~BlockArchiveDirectory()
{
    (void)close(archive_fd_);
    monad_bcap_archive_close(archive_);
}

std::string BlockArchiveDirectory::describe() const
{
    return std::format("{} [block archive]", origin_path_.string());
}

std::string
BlockArchiveDirectory::validate(EventSourceSpec const &source_spec) const
{
    EventSourceQuery const &q = source_spec.source_query;

    if (q.block && q.block->type == BlockLabel::Type::BlockId) {
        return "querying block archive by start block ID not supported yet";
    }
    if (q.consensus_event) {
        return "block archives do not support consensus event search";
    }

    // XXX: maybe we shouldn't do a full verification of the block
    // archive (including missing blocks) during input validation,
    // but it seems fast enough for now
    uint64_t first_block = source_spec.source_query.block
                               ? source_spec.source_query.block->block_number
                               : 0;
    if (first_block == 0 &&
        monad_bcap_archive_find_minmax(archive_, &first_block, nullptr) != 0) {
        return monad_bcap_get_last_error();
    }

    if (first_block == 0 || (q.count && *q.count == 0)) {
        return {}; // Empty range is OK
    }
    uint64_t const last_block =
        q.count ? first_block + *q.count - 1 : MONAD_BCAP_SEARCH_NO_LIMIT;

    monad_bcap_block_range_list missing_ranges;
    monad_bcap_block_range_list_init(&missing_ranges);
    if (monad_bcap_archive_find_missing(
            archive_, first_block, last_block, &missing_ranges) != 0) {
        return monad_bcap_get_last_error();
    }
    if (!TAILQ_EMPTY(&missing_ranges.head)) {
        size_t missing_count;
        std::string const m =
            format_missing_block_range_list(missing_ranges, &missing_count);
        monad_bcap_block_range_list_free(&missing_ranges);
        return std::format(
            "archive is missing {} blocks: {}", missing_count, m);
    }

    // XXX: it would be nice to validate whether we have a trace archive, etc.
    // but this probably needs to be done at the command level
#if 0
    // Check that at least the first block conforms to the contents that
    // the query is expecting; we don't do this for every block
    monad_evcap_reader *evcap_reader;
    monad_evcap_section_desc const *event_sd;
    char path_buf[64];
    int const rc = monad_bcap_archive_open_block_reader(
        archive_,
        first_block,
        path_buf,
        sizeof path_buf,
        nullptr,
        &evcap_reader,
        &event_sd);
    if (rc != 0) {
        return std::format(
            "bcap library error -- {}", monad_bcap_get_last_error());
    }

    auto const opt_resolved =
            lookup_capture_section(get_type(), evcap_reader, source_spec.source_query);
    monad_evcap_reader_destroy(evcap_reader);
#endif

    // Static sequence number checks
    bool const has_seqno_bounds =
        source_spec.opt_begin_seqno || source_spec.opt_end_seqno;
    bool const has_single_block = !q.count || *q.count == 1;
    if (has_seqno_bounds && !has_single_block) {
        return std::format("--begin-seqno/--end-seqno cannot be specified on "
                           "multi-block iteration");
    }

    return {};
}

std::string BlockArchiveDirectory::init_iterator(
    EventIterator *iter, EventSourceSpec const &source_spec) const
{
    EventSourceQuery const &q = source_spec.source_query;

    iter->iter_type = EventIterator::Type::BlockArchive;
    iter->content_type = MONAD_EVENT_CONTENT_TYPE_NONE;
    iter->finished = false;
    iter->error_code = 0;
    iter->last_error_msg = nullptr;

    uint64_t first_block = source_spec.source_query.block
                               ? source_spec.source_query.block->block_number
                               : 0;
    if (first_block == 0 &&
        monad_bcap_archive_find_minmax(archive_, &first_block, nullptr) != 0) {
        return monad_bcap_get_last_error();
    }
    if (first_block == 0 || (q.count && *q.count == 0)) {
        iter->finished = true;
        return {}; // Empty block archive
    }

    monad_evcap_reader *evcap_reader;
    int fd;
    char path_buf[64];
    int const rc = monad_bcap_archive_open_block_reader(
        archive_,
        first_block,
        path_buf,
        sizeof path_buf,
        &fd,
        &evcap_reader,
        nullptr);
    if (rc != 0) {
        return std::format(
            "cannot open evcap reader for block {} iterator -- {}",
            first_block,
            monad_bcap_get_last_error());
    }

    auto const opt_resolved =
        lookup_capture_section(get_type(), evcap_reader, q);
    if (!opt_resolved) {
        return std::format("no section in archive block {}", first_block);
    }
    if (opt_resolved->resolved_sd->type != MONAD_EVCAP_SECTION_EVENT_BUNDLE) {
        return std::format(
            "resolved section in archive block {} has the wrong type ({} not "
            "{})",
            first_block,
            g_monad_evcap_section_names[opt_resolved->resolved_sd->type],
            g_monad_evcap_section_names[MONAD_EVCAP_SECTION_EVENT_BUNDLE]);
    }
    MONAD_ASSERT(opt_resolved->schema_sd != nullptr);
    iter->content_type = opt_resolved->schema_sd->schema.content_type;

    iter->archive.cur_capture_file = std::make_unique<EventCaptureFile>(
        origin_path_ / fs::path{path_buf}, fd, evcap_reader);
    iter->archive.archive_dir = this;
    iter->archive.source_spec = &source_spec;
    iter->archive.blocks_consumed = 0;

    EventIterator::CaptureSectionImpl &cs = iter->archive.open_section;
    cs.capture_file = iter->archive.cur_capture_file.get();
    cs.section_limit = 1;
    if (monad_evcap_event_section_open(
            &cs.cur_section, evcap_reader, opt_resolved->resolved_sd) != 0) {
        errx_f(
            EX_SOFTWARE,
            "evcap library error opening iterator to section {} in {} inside "
            "{}-- {}",
            opt_resolved->resolved_sd->index,
            iter->archive.cur_capture_file->describe(),
            describe(),
            monad_evcap_reader_get_last_error());
    }

    monad_evcap_event_section_open_iterator(&cs.cur_section, &cs.iter);
    if (source_spec.opt_begin_seqno) {
        iter->begin_seqno =
            monad_evsrc_iter_set_seqno(
                &cs.iter, *source_spec.opt_begin_seqno) == MONAD_EVSRC_SUCCESS
                ? source_spec.opt_begin_seqno
                : std::nullopt;
    }
    if (source_spec.opt_end_seqno) {
        monad_evcap_event_iter dummy_iter;
        monad_evcap_event_section_open_iterator(&cs.cur_section, &dummy_iter);
        iter->end_seqno =
            monad_evsrc_iter_set_seqno(
                &dummy_iter, *source_spec.opt_end_seqno) == MONAD_EVSRC_SUCCESS
                ? source_spec.opt_end_seqno
                : std::nullopt;
    }

    return {};
}

std::optional<ResolvedCaptureSections> lookup_capture_section(
    EventSourceFile::Type source_file_type,
    monad_evcap_reader const *evcap_reader, EventSourceQuery const &q)
{
    using enum CaptureSectionSpec::SeekOrigin;

    monad_evcap_section_type filter = MONAD_EVCAP_SECTION_NONE;
    monad_evcap_section_desc const *scan_sd = nullptr;
    monad_evcap_section_desc const *schema_sd = nullptr;
    size_t section_count = 0;

    if (source_file_type == EventSourceFile::Type::EventCaptureFile &&
        q.block && !q.consensus_event) {
        return lookup_capture_section_with_block(evcap_reader, q);
    }

    // When there's no capture specification, take the first event bundle
    // section in the file
    CaptureSectionSpec css = q.section.value_or(CaptureSectionSpec{
        .origin = SectionType,
        .section_type = MONAD_EVCAP_SECTION_EVENT_BUNDLE});

    switch (css.origin) {
    case Absolute:
        filter = MONAD_EVCAP_SECTION_NONE;
        break;
    case SectionType:
        filter = css.section_type;
        break;
    case Unspecified:
        // XXX: this is ambiguous, not clear what to do here
        css.section_type = MONAD_EVCAP_SECTION_EVENT_BUNDLE;
        [[fallthrough]];
    case ContentType:
        filter = MONAD_EVCAP_SECTION_EVENT_BUNDLE;
        break;
    }

    while (monad_evcap_reader_next_section(evcap_reader, filter, &scan_sd)) {
        schema_sd =
            scan_sd->type == MONAD_EVCAP_SECTION_EVENT_BUNDLE
                ? monad_evcap_reader_load_linked_section_desc(
                      evcap_reader, scan_sd->event_bundle.schema_desc_offset)
                : nullptr;

        switch (css.origin) {
        case Unspecified:
            std::unreachable(); // Re-written to section type
        case Absolute:
            [[fallthrough]];
        case SectionType:
            if (!css.offset || css.offset == section_count++) {
                return ResolvedCaptureSections{scan_sd, schema_sd};
            }
            break;
        case ContentType:
            if (schema_sd->schema.content_type == css.content_type &&
                (!css.offset || css.offset == section_count++)) {
                return ResolvedCaptureSections{scan_sd, schema_sd};
            }
        }
    }

    return std::nullopt;
}
