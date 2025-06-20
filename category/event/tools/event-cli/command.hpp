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

#include "options.hpp"

#include <concepts>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <format>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <category/core/hex.hpp>

enum monad_evcap_section_type : uint16_t;
enum monad_event_content_type : uint16_t;
enum monad_exec_event_type : uint16_t;

struct Command;
struct EventIterator;

class EventCaptureFile;
class EventSourceFile;

// Represents a block number or block ID
struct BlockLabel
{
    enum class Type
    {
        BlockNumber,
        BlockId,
    };
    Type type;
    uint64_t block_number;
    std::vector<uint8_t> block_id;
};

// Explicit selection of a particular section in an event capture file
struct CaptureSectionSpec
{
    // Offset is interpreted relative to this
    enum class SeekOrigin
    {
        Unspecified,
        Absolute,
        SectionType,
        ContentType,
    };

    SeekOrigin origin;

    union
    {
        monad_evcap_section_type section_type;
        monad_event_content_type content_type;
    };

    std::optional<uint64_t> offset;

    [[nodiscard]] std::string describe() const;
};

// An event source specification can have a URI-like query component, which
// selects a part an event source file in some way. It can be used to select
// a particular section of an event capture file, a particular block in a
// block archive directory, etc. This object represents the parsed form of
// the query
struct EventSourceQuery
{
    std::optional<CaptureSectionSpec> section;
    std::optional<BlockLabel> block;
    std::optional<uint64_t> count;
    std::optional<monad_exec_event_type> consensus_event;

    [[nodiscard]] std::string describe() const;
};

// Represents a fully-parsed event source specification, plus the sequence
// number limit options that are sometimes present
struct EventSourceSpec
{
    EventSourceFile *source_file;
    EventSourceQuery source_query;
    std::optional<uint64_t> opt_begin_seqno;
    std::optional<uint64_t> opt_end_seqno;

    [[nodiscard]] std::string describe() const;

    [[nodiscard]] std::string init_iterator(EventIterator *) const;
};

struct OutputFile
{
    ~OutputFile()
    {
        if (file && file != stdout && file != stderr) {
            std::fclose(file);
        }
    }

    std::filesystem::path canonical_path;
    std::FILE *file;
};

struct Command
{
    enum class Type
    {
        BlockStat,
        Digest,
        Dump,
        ExecStat,
        HeadStat,
        Info,
        Record,
        RecordExec,
        SectionDump,
        Snapshot,
    };

    explicit Command(
        Type t, std::vector<EventSourceSpec> s, OutputFile *o,
        void const *parsed_opts)
        : type{t}
        , event_sources{std::move(s)}
        , output{o}
        , options{parsed_opts}
    {
    }

    bool has_type(Type t) const
    {
        return type == t;
    }

    CommonCommandOptions const *get_common_options() const
    {
        return static_cast<CommonCommandOptions const *>(options);
    }

    template <typename T>
    T const *get_options() const
    {
        T const *cast = static_cast<T const *>(options);
        switch (type) {
        case Type::BlockStat:
            return std::same_as<T, BlockStatCommandOptions> ? cast : nullptr;
        case Type::Digest:
            return std::same_as<T, DigestCommandOptions> ? cast : nullptr;
        case Type::Dump:
            return std::same_as<T, DumpCommandOptions> ? cast : nullptr;
        case Type::ExecStat:
            return std::same_as<T, ExecStatCommandOptions> ? cast : nullptr;
        case Type::HeadStat:
            return std::same_as<T, HeadStatCommandOptions> ? cast : nullptr;
        case Type::Info:
            return std::same_as<T, InfoCommandOptions> ? cast : nullptr;
        case Type::Record:
            return std::same_as<T, RecordCommandOptions> ? cast : nullptr;
        case Type::RecordExec:
            return std::same_as<T, RecordExecCommandOptions> ? cast : nullptr;
        case Type::SectionDump:
            return std::same_as<T, SectionDumpCommandOptions> ? cast : nullptr;
        case Type::Snapshot:
            return std::same_as<T, SnapshotCommandOptions> ? cast : nullptr;
        default:
            return nullptr;
        }
    }

    Type type;
    std::vector<EventSourceSpec> event_sources;
    OutputFile *output;
    void const *options;
};

void run_info_command(Command const *);
void run_sectiondump_command(Command const *);

void headstat_thread_main(Command const *);

constexpr char const *describe(Command::Type t)
{
    using enum Command::Type;
    switch (t) {
    case BlockStat:
        return "blockstat";
    case Digest:
        return "digest";
    case Dump:
        return "dump";
    case ExecStat:
        return "execstat";
    case HeadStat:
        return "headstat";
    case Info:
        return "info";
    case Record:
        return "record";
    case RecordExec:
        return "recordexec";
    case SectionDump:
        return "sectiondump";
    case Snapshot:
        return "snapshot";
    }
    std::unreachable();
}

template <>
struct std::formatter<BlockLabel> : std::formatter<std::string_view>
{
    template <class FmtContext>
    FmtContext::iterator format(BlockLabel const &b, FmtContext &ctx) const
    {
        if (b.type == BlockLabel::Type::BlockNumber) {
            std::string const s = std::format("{}", b.block_number);
            return this->std::formatter<std::string_view>::format(
                std::string_view{s}, ctx);
        }
        std::span<uint8_t const> const bytes = std::span{b.block_id};
        std::string const s = std::format("{}", monad::as_hex(bytes));
        return this->std::formatter<std::string_view>::format(
            std::string_view{s}, ctx);
    }
};
