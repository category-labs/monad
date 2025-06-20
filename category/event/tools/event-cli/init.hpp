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

#include "command.hpp"
#include "options.hpp"
#include "stream.hpp"

#include <filesystem>
#include <memory>
#include <span>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <sys/types.h>

struct Command;

class EventSourceFile;

using EventSourceFileMap =
    std::unordered_map<ino_t, std::unique_ptr<EventSourceFile>>;
using NamedInputMap = std::unordered_map<std::string, std::filesystem::path>;
using OutputFileMap = std::unordered_map<ino_t, std::unique_ptr<OutputFile>>;

using StreamThreadMap =
    std::unordered_map<std::string, std::vector<StreamObserver *>>;

struct Topology
{
    std::vector<std::unique_ptr<Command>> commands;
    std::vector<std::unique_ptr<StreamObserver>> stream_observers;
    EventSourceFileMap event_source_files;
    StreamThreadMap stream_thread_map;
    OutputFileMap output_file_map;
};

extern int run_commands(Topology);

class CommandBuilder
{
public:
    explicit CommandBuilder(
        std::span<std::pair<std::string, std::string> const> named_input_specs,
        std::span<std::string const> force_live_specs);

    Topology finish();

    Command *build_blockstat_command(BlockStatCommandOptions const &);
    Command *build_digest_command(DigestCommandOptions const &);
    Command *build_dump_command(DumpCommandOptions const &);
    Command *build_execstat_command(ExecStatCommandOptions const &);
    Command *build_headstat_command(HeadStatCommandOptions const &);
    Command *build_info_command(InfoCommandOptions const &);
    Command *build_record_command(RecordCommandOptions const &);
    Command *build_recordexec_command(RecordExecCommandOptions const &);
    Command *build_sectiondump_command(SectionDumpCommandOptions const &);
    Command *build_snapshot_command(SnapshotCommandOptions const &);

private:
    Command *build_basic_command(
        Command::Type, CommonCommandOptions const &, bool set_output);

    Topology topology_;
    NamedInputMap named_input_map_;
    std::unordered_set<ino_t> force_live_set_;
};
