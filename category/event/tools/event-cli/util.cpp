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

#include "util.hpp"
#include "command.hpp"
#include "err_cxx.hpp"
#include "options.hpp"

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <expected>
#include <format>
#include <iterator>
#include <optional>
#include <print>
#include <span>
#include <string>
#include <utility>

#include <stdio.h>
#include <sysexits.h>
#include <unistd.h>

#include <category/core/assert.h>
#include <category/core/event/evcap_file.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/event/blockcap.h>

#include <zstd.h>

namespace
{

char const *describe(monad_evcap_section_compression c)
{
    switch (c) {
    case MONAD_EVCAP_COMPRESSION_NONE:
        return "*";
    case MONAD_EVCAP_COMPRESSION_ZSTD_SINGLE_PASS:
        return "Z1P";
    case MONAD_EVCAP_COMPRESSION_ZSTD_STREAMING:
        return "ZST";
    default:
        return "?";
    }
}

std::string describe(monad_bcap_block_range const &r)
{
    return r.min == r.max ? std::format("{}", r.min)
                          : std::format("[{}, {}]", r.min, r.max);
}

char const *get_content_name_safe(monad_event_content_type_t content_type)
{
    return content_type < std::size(g_monad_event_content_type_names)
               ? g_monad_event_content_type_names[content_type]
               : "??";
}

} // End of anonymous namespace

std::expected<ZSTD_CCtx *, std::string>
create_zstd_cctx(std::optional<uint8_t> const &compression_level)
{
    if (!compression_level) {
        return nullptr;
    }
    ZSTD_CCtx *const cctx = ZSTD_createCCtx();
    if (cctx == nullptr) {
        return std::unexpected("ZSTD_createCCtx failed");
    }
    size_t const r = ZSTD_CCtx_setParameter(
        cctx, ZSTD_c_compressionLevel, *compression_level);
    if (ZSTD_isError(r)) {
        ZSTD_freeCCtx(cctx);
        return std::unexpected(std::format(
            "ZSTD_CCtx_setParameter failed for level {}: {}",
            *compression_level,
            ZSTD_getErrorName(r)));
    }
    return cctx;
}

bool event_ring_is_abandoned(int ring_fd)
{
    constexpr size_t MAX_FLOCKS = 128;
    monad_event_flock_info flocks[MAX_FLOCKS];
    size_t lock_count = std::size(flocks);
    if (monad_event_ring_query_flocks(ring_fd, flocks, &lock_count) != 0) {
        errx_f(
            EX_SOFTWARE,
            "event library error -- {}",
            monad_event_ring_get_last_error());
    }
    return lock_count == 0;
}

std::string expect_content_type(
    EventSourceSpec const &event_source, monad_event_content_type expected,
    monad_event_content_type actual)
{
    if (expected != actual) {
        return std::format(
            "expected event source {} with content type `{}` "
            "[{}] but content type `{}` [{}] was found",
            event_source.describe(),
            g_monad_event_content_type_names[expected],
            std::to_underlying(expected),
            g_monad_event_content_type_names[actual],
            std::to_underlying(actual));
    }
    return {};
}

std::string format_missing_block_range_list(
    monad_bcap_block_range_list const &list, size_t *missing_count_p)
{
    size_t missing_count = 0;
    std::string s;
    monad_bcap_block_range const *r = TAILQ_FIRST(&list.head);
    missing_count += r->max - r->min + 1;
    s += std::format("{}", describe(*r));
    while ((r = TAILQ_NEXT(r, next)) != nullptr) {
        missing_count += r->max - r->min + 1;
        s += std::format(", {}", describe(*r));
    }
    if (missing_count_p != nullptr) {
        *missing_count_p = missing_count;
    }
    return s;
}

void print_evcap_sectab_header(std::FILE *out)
{
    // Print section table header
    // <index> [<tab>:<ent>] <section-type> <offset> <file-length>
    //    <compressed-length> <extra>
    std::println(
        out,
        "{:>6} {:>3}:{:<4} {:20} {:>12} {:>5} {:>12} {:>12} {:>12} {}",
        "INDEX",
        "TAB",
        "ENT",
        "SECTION_TYPE",
        "DESC_OFF",
        "COM",
        "CONTENT_OFF",
        "CONTENT_LEN",
        "FILE_LEN",
        "EXTRA");
}

void print_evcap_sectab_entry(
    monad_evcap_file_header const &fh, monad_evcap_section_desc const &sd,
    std::span<monad_bcap_pack_index_entry const> pack_index_table,
    std::FILE *out)
{
    uint32_t const sectab_entries = monad_evcap_get_sectab_entries(&fh);
    std::print(
        out,
        "{:6} {:3}:{:<4} {:16} [{}] {:12} {:>5} {:12} {:12} {:12}",
        sd.index,
        sd.index / sectab_entries,
        sd.index % sectab_entries,
        g_monad_evcap_section_names[sd.type],
        std::to_underlying(sd.type),
        sd.descriptor_offset,
        describe(sd.compression),
        sd.content_offset,
        sd.content_length,
        sd.file_length);

    switch (sd.type) {
    case MONAD_EVCAP_SECTION_SCHEMA:
        std::print(
            out,
            "   CONTENT_TYPE: {:6} [{}] HASH: {:{#}}",
            get_content_name_safe(sd.schema.content_type),
            std::to_underlying(sd.schema.content_type),
            monad::as_hex(std::span{sd.schema.schema_hash}.first(4)));
        break;

    case MONAD_EVCAP_SECTION_EVENT_BUNDLE:
        if (sd.event_bundle.pack_index_id == 0 || empty(pack_index_table)) {
            std::print(
                out,
                "   SCH_OFF: {} #EVT: {} SSEQ: {} SIDX_OFF: {} BLK: {}",
                sd.event_bundle.schema_desc_offset,
                sd.event_bundle.event_count,
                sd.event_bundle.start_seqno,
                sd.event_bundle.seqno_index_desc_offset,
                sd.event_bundle.block_number);
        }
        else {
            // We have a block index section descriptor (which usually
            // appears before event bundles because of how the writer
            // works)
            monad_bcap_pack_index_entry const &index_entry =
                pack_index_table[sd.event_bundle.pack_index_id - 1];
            std::print(
                out,
                "   BLK: {:9} EVT: {:6} SIDX_OFF: {}",
                index_entry.block_number,
                sd.event_bundle.event_count,
                sd.event_bundle.seqno_index_desc_offset);
        }
        break;

    case MONAD_EVCAP_SECTION_SEQNO_INDEX:
        std::print(
            out, "   EB_OFF: {}", sd.seqno_index.event_bundle_desc_offset);
        break;

    case MONAD_EVCAP_SECTION_PACK_INDEX:
        std::print(
            out,
            "   ACT: {:c} START: {} END: {} CAP: {}",
            __atomic_load_n(&sd.pack_index.is_active, __ATOMIC_ACQUIRE) ? 'Y'
                                                                        : 'N',
            sd.pack_index.start_block,
            sd.pack_index.start_block +
                __atomic_load_n(&sd.pack_index.block_count, __ATOMIC_ACQUIRE),
            sd.pack_index.entry_capacity);
        break;

    case MONAD_EVCAP_SECTION_NONE:
        [[fallthrough]];
    case MONAD_EVCAP_SECTION_COUNT:
        MONAD_ABORT_PRINTF(
            "%hu section should not be returned by iterator", sd.type);
    }
    std::println(out);
}

bool use_tty_control_codes(TextUIMode tui_mode, OutputFile const *output)
{
    switch (tui_mode) {
    case TextUIMode::Always:
        return true;
    case TextUIMode::Never:
        return false;
    case TextUIMode::Auto:
        break; // Handled in the body of the function
    }
    if (int const rc = isatty(fileno(output->file)); rc == -1) {
        err_f(
            EX_OSERR,
            "isatty on output `{}` failed",
            output->canonical_path.string());
    }
    else {
        return static_cast<bool>(rc);
    }
}
