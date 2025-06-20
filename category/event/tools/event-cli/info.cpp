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

#include "command.hpp"
#include "file.hpp"
#include "options.hpp"
#include "util.hpp"

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <format>
#include <iterator>
#include <print>
#include <ranges>
#include <span>
#include <utility>
#include <vector>

#include <sys/queue.h>

#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_reader.h>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/event/blockcap.h>

namespace
{

void print_event_ring_headers(
    std::span<MappedEventRing const *const> rings, std::FILE *out)
{
    // Print the event ring file header information:
    // <type-name> [<type-code>] <descriptor capacity> <descriptor byte size>
    //    <payload buf size> <context area size> <last write seqno>
    //    <next payload buf byte> <pbuf window start> <meta-hash> <file-name>
    std::println(
        out,
        "{:10} {:>9} {:>10} {:>10} {:>10} {:>12} {:>14} {:>14} {:14} {}",
        "TYPE",
        "DESC_CAP",
        "DESC_SZ",
        "PBUF_SZ",
        "CTX_SZ",
        "WR_SEQNO",
        "PBUF_NEXT",
        "PBUF_WIN",
        "METADATA_HASH",
        "FILE_NAME");
    for (MappedEventRing const *mr : rings) {
        using monad::as_hex;
        monad_event_ring_header const *const h = mr->get_header();
        std::println(
            out,
            "{:6} [{}] {:9} {:10} {:10} {:10} {:12} {:14} {:14} {:{#}14} {}",
            g_monad_event_content_type_names[h->content_type],
            std::to_underlying(h->content_type),
            h->size.descriptor_capacity,
            h->size.descriptor_capacity * sizeof(monad_event_descriptor),
            h->size.payload_buf_size,
            h->size.context_area_size,
            __atomic_load_n(&h->control.last_seqno, __ATOMIC_ACQUIRE),
            __atomic_load_n(&h->control.next_payload_byte, __ATOMIC_ACQUIRE),
            __atomic_load_n(&h->control.buffer_window_start, __ATOMIC_ACQUIRE),
            as_hex(std::span{h->schema_hash}.first(4)),
            mr->describe());
    }
}

void print_event_capture_header(
    std::string_view description, monad_evcap_reader const *const evcap_reader,
    bool print_full_section_table, std::FILE *out)
{
    monad_evcap_file_header const *const file_header =
        monad_evcap_reader_get_file_header(evcap_reader);

    std::println(
        out,
        "{} with {} sections in {} section table(s) (size {}):",
        description,
        file_header->section_count,
        file_header->sectab_count,
        monad_evcap_get_sectab_entries(file_header));
    std::print(out, "SECTAB OFFSETS:");
    for (uint8_t t = 0; t < file_header->sectab_count; ++t) {
        std::print(out, " {}", file_header->sectab_offsets[t]);
    }
    std::println(out);

    std::byte const *const map_base = reinterpret_cast<std::byte const *>(
        monad_evcap_reader_get_mmap_base(evcap_reader));
    monad_evcap_section_desc const *sd = nullptr;
    std::span<monad_bcap_pack_index_entry const> pack_index_table;

    while (monad_evcap_reader_next_section(
        evcap_reader, MONAD_EVCAP_SECTION_NONE, &sd)) {
        if (sd->index == 0) {
            print_evcap_sectab_header(out);
        }
        print_evcap_sectab_entry(*file_header, *sd, pack_index_table, out);

        switch (sd->type) {
        case MONAD_EVCAP_SECTION_PACK_INDEX:
            pack_index_table = std::span{
                reinterpret_cast<monad_bcap_pack_index_entry const *>(
                    map_base + sd->content_offset),
                sd->pack_index.block_count};
            break;
        default:
            break;
        }

        if (!print_full_section_table && sd->index > 10) {
            std::println(
                "skipping {} additional sections...",
                file_header->section_count - sd->index - 1);
            break;
        }
    }
}

void print_block_archive_info(
    BlockArchiveDirectory const *archive, std::FILE *out)
{
    uint64_t min_block;
    uint64_t max_block;
    monad_bcap_block_range_list missing_ranges;
    size_t missing_count = 0;

    std::println(out, "{} information:", archive->describe());
    if (monad_bcap_archive_find_minmax(
            archive->get_block_archive(), &min_block, &max_block) != 0) {
        std::println(
            out, "bcap library error -- {}", monad_bcap_get_last_error());
        return;
    }
    monad_bcap_block_range_list_init(&missing_ranges);
    if (monad_bcap_archive_find_missing(
            archive->get_block_archive(),
            min_block,
            max_block,
            &missing_ranges) != 0) {
        std::println(
            out, "bcap library error -- {}", monad_bcap_get_last_error());
        return;
    }

    std::println(out, "     first block: {}", min_block);
    std::println(out, "      last block: {}", max_block);
    std::print(out, "  missing blocks: ");

    if (TAILQ_EMPTY(&missing_ranges.head)) {
        std::println(out, "<none>");
    }
    else {
        std::println(
            out,
            "{}",
            format_missing_block_range_list(missing_ranges, &missing_count));
    }
    size_t const total_blocks =
        min_block == 0 ? 0 : max_block - min_block + 1 - missing_count;
    std::println(
        out, "    total blocks: {} [{} missing]", total_blocks, missing_count);
    monad_bcap_block_range_list_free(&missing_ranges);
}

void print_block_archive_capture_file_info(
    BlockArchiveDirectory const *archive, uint64_t begin_block,
    uint64_t end_block, std::FILE *out)
{
    for (uint64_t block_number = begin_block; block_number < end_block;
         ++block_number) {
        char pathbuf[64];
        monad_evcap_reader *evcap_reader;

        if (monad_bcap_archive_open_block_reader(
                archive->get_block_archive(),
                block_number,
                pathbuf,
                sizeof pathbuf,
                nullptr,
                &evcap_reader,
                nullptr) != 0) {
            std::println(
                out, "bcap library error -- {}", monad_bcap_get_last_error());
            return;
        }
        print_event_capture_header(
            std::format("block {} [{}]", block_number, pathbuf),
            evcap_reader,
            true,
            out);
        monad_evcap_reader_destroy(evcap_reader);
    }
}

} // End of anonymous namespace

void run_info_command(Command const *command)
{
    std::span<EventSourceSpec const> const event_sources =
        command->event_sources;
    std::FILE *const out = command->output->file;
    auto const *const options = command->get_options<InfoCommandOptions>();

    auto const is_event_ring = [](EventSourceSpec const &ess) {
        return ess.source_file->get_type() == EventSourceFile::Type::EventRing;
    };
    auto const extract_event_ring = [](EventSourceSpec const &ess) {
        return static_cast<MappedEventRing const *>(ess.source_file);
    };
    auto event_ring_range = event_sources | std::views::filter(is_event_ring) |
                            std::views::transform(extract_event_ring);

    std::vector<MappedEventRing const *> const rings{
        std::from_range, event_ring_range};
    if (!empty(rings)) {
        print_event_ring_headers(rings, out);
    }

    auto const is_capture_file = [](EventSourceSpec const &ess) {
        return ess.source_file->get_type() ==
               EventSourceFile::Type::EventCaptureFile;
    };
    for (size_t i = 0; EventSourceSpec const &ess :
                       event_sources | std::views::filter(is_capture_file)) {
        if (i++ == 0) {
            std::println(out, "Event capture files:");
        }
        // XXX: maybe filter this by the query
        print_event_capture_header(
            ess.source_file->describe(),
            static_cast<EventCaptureFile const *>(ess.source_file)
                ->get_reader(),
            options->full_evcap_section_table,
            out);
    }

    auto const is_archive_dir = [](EventSourceSpec const &ess) {
        return ess.source_file->get_type() ==
               EventSourceFile::Type::BlockArchiveDirectory;
    };
    for (size_t i = 0; EventSourceSpec const &ess :
                       event_sources | std::views::filter(is_archive_dir)) {
        if (i++ == 0) {
            std::println(out, "Block archive directories:");
        }
        auto archive =
            static_cast<BlockArchiveDirectory const *>(ess.source_file);
        if (ess.source_query.block) {
            if (ess.source_query.block->type != BlockLabel::Type::BlockNumber) {
                std::println(out, "info: only block number queries permitted");
                continue;
            }
            uint64_t const begin = ess.source_query.block->block_number;
            uint64_t const end = begin + ess.source_query.count.value_or(1);
            print_block_archive_capture_file_info(archive, begin, end, out);
        }
        else {
            print_block_archive_info(archive, out);
        }
    }
}
