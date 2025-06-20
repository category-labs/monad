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

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <expected>
#include <optional>
#include <span>
#include <string>
#include <utility>

#include <sys/queue.h>

enum monad_event_content_type : uint16_t;

struct monad_bcap_block_range_list;
struct monad_bcap_pack_index_entry;
struct monad_evcap_file_header;
struct monad_evcap_section_desc;

enum class TextUIMode : unsigned;

struct EventSourceSpec;
struct OutputFile;

class EventCaptureFile;

typedef struct ZSTD_CCtx_s ZSTD_CCtx;

std::expected<ZSTD_CCtx *, std::string>
create_zstd_cctx(std::optional<uint8_t> const &compression_level);

bool event_ring_is_abandoned(int ring_fd);

std::string expect_content_type(
    EventSourceSpec const &, monad_event_content_type expected,
    monad_event_content_type actual);

std::string format_missing_block_range_list(
    monad_bcap_block_range_list const &, size_t *missing_count);

void print_evcap_sectab_header(std::FILE *);

void print_evcap_sectab_entry(
    monad_evcap_file_header const &, monad_evcap_section_desc const &,
    std::span<monad_bcap_pack_index_entry const> pack_index_table, std::FILE *);

bool use_tty_control_codes(TextUIMode, OutputFile const *);

constexpr std::string ANSI_MoveCursorTopLeft = "\x1b[H";
constexpr std::string ANSI_ClearFromCursorToEnd = "\x1b[J";
constexpr std::string ANSI_ClearScreen = "\x1b[2J";

constexpr std::string ANSI_HideCursor = "\x1b[?25l";
constexpr std::string ANSI_ShowCursor = "\x1b[?25h";

// If we don't hide the cursor first, resetting to (1,1) renders poorly on some
// terminals
constexpr std::string ANSI_ResetCursor =
    ANSI_HideCursor + ANSI_MoveCursorTopLeft;

// When we're done writing a table that updates, clear the rest of the screen
// and show the cursor again
constexpr std::string ANSI_FinishUpdate =
    ANSI_ClearFromCursorToEnd + ANSI_ShowCursor;
