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
#include "init.hpp"
#include "options.hpp"

#include <array>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include <category/core/event/event_def.h>

#include <CLI/CLI.hpp>

namespace
{

void add_common_options(
    CLI::App *subcommand, CommonCommandOptions &options,
    std::string_view subcommand_verb)
{
    CLI::Option *const source_opt =
        subcommand
            ->add_option(
                "-s,--source",
                options.event_source_spec,
                "Event ring, capture file, archive directory, or --input name")
            ->type_name("<event-source-spec>");
    if (!empty(options.event_source_spec)) {
        source_opt->default_val(options.event_source_spec)
            ->capture_default_str();
    }
    subcommand
        ->add_option(
            "-t,--thread",
            options.thread,
            std::format("Thread to run {} reader on", subcommand_verb))
        ->type_name("<thread-name>");
    subcommand
        ->add_option(
            "-o,--output",
            options.output_spec,
            std::format("Output file for {}", subcommand_verb))
        ->type_name("<output>");
}

void add_seqno_range_options(
    CLI::App *subcommand, CommonCommandOptions &options)
{
    subcommand
        ->add_option(
            "-b,--begin",
            options.begin_seqno,
            "Start iteration at this sequence number")
        ->type_name("<seqno>");
    subcommand
        ->add_option(
            "-e,--end",
            options.end_seqno,
            "Stop iteration at this sequence number")
        ->type_name("<seqno>");
}

CLI::Option *add_tui_mode_option(CLI::App *subcommand, TextUIMode &tui_mode)
{
    return subcommand
        ->add_option(
            "-m,--mode", tui_mode, "When to emit control characters for TUI")
        ->default_val(TextUIMode::Auto)
        ->capture_default_str()
        ->type_name("<tui-mode>")
        ->transform(CLI::CheckedTransformer(
            std::unordered_map<std::string, TextUIMode>{
                {"yes", TextUIMode::Always},
                {"no", TextUIMode::Never},
                {"auto", TextUIMode::Auto}},
            CLI::ignore_case));
}

} // end of anonymous namespace

int main(int argc, char **argv)
{
    bool print_stream_stats = false;

    BlockStatCommandOptions blockstat_var{};
    std::vector<BlockStatCommandOptions> blockstat_commands;

    DigestCommandOptions digest_var{};
    std::vector<DigestCommandOptions> digest_commands;

    DumpCommandOptions dump_var{};
    std::vector<DumpCommandOptions> dump_commands;

    ExecStatCommandOptions execstat_var{};
    std::vector<ExecStatCommandOptions> execstat_commands;

    RecordCommandOptions record_var{};
    std::vector<RecordCommandOptions> record_commands;

    RecordExecCommandOptions recordexec_var{};
    std::vector<RecordExecCommandOptions> recordexec_commands;

    SnapshotCommandOptions snapshot_var{};
    std::vector<SnapshotCommandOptions> snapshot_commands;

    HeadStatCommandOptions headstat_command{};
    InfoCommandOptions info_command{};
    SectionDumpCommandOptions sectiondump_command{};

    std::vector<std::pair<std::string, std::string>> input_specs;
    std::vector<std::string> force_live_specs;

    CLI::App cli{"monad event command line tool"};
    cli.set_help_all_flag(
        "--help-all", "Show full help, including all subcommands");

    cli.add_option("-i,--input", input_specs, "Add named event source file")
        ->type_name("<input-name>:<file-or-ring-type>")
        ->type_size(-2)
        ->delimiter(':');

    // This option is used when the `event_ring_is_abandoned` logic doesn't
    // work, e.g., because the writer lives inside a docker container with a
    // different process namespace (i.e., we can't scrape procfs)
    cli.add_option(
           "-f,--force-live",
           force_live_specs,
           "Force event rings to appear alive")
        ->type_name("<ring-spec>")
        ->delimiter(',');

    cli.add_flag(
        "--stream-stats",
        print_stream_stats,
        "Print stream processing statistics to stderr");

    cli.require_subcommand(1, 0);

    /*
     * blockstat command
     */

    CLI::App *const blockstat = cli.add_subcommand(
        "blockstat", "Compute aggregate statistics about blocks");
    add_common_options(blockstat, blockstat_var.common_options, "blockstat");
    add_seqno_range_options(blockstat, blockstat_var.common_options);
    blockstat->alias("bs");
    blockstat_var.common_options.event_source_spec =
        g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_EXEC];
    blockstat->add_flag(
        "--blocks",
        blockstat_var.display_blocks,
        "Display information about each block");
    CLI::Option *const outliers_opt =
        blockstat
            ->add_option(
                "--outliers",
                blockstat_var.outlier_size,
                "Size of outlier table to display at the end")
            ->check(CLI::Range(0, 1000));
    blockstat
        ->add_option(
            "--long-txn-time-min-txn",
            blockstat_var.long_txn_time_min_txn,
            "Minimum number of txns to be included as a long txn time outlier")
        ->needs(outliers_opt);
    blockstat
        ->add_option(
            "--gas-efficiency-min-txn",
            blockstat_var.gas_efficiency_min_txn,
            "Minimum number of txns to be included as a gas efficiency outlier")
        ->needs(outliers_opt);
    blockstat->immediate_callback();
    blockstat->callback([&blockstat_var, &blockstat_commands] {
        blockstat_commands.push_back(blockstat_var);
        blockstat_var = {};
        blockstat_var.common_options.event_source_spec =
            g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_EXEC];
    });

    /*
     * digest subcommand
     */

    CLI::App *const digest = cli.add_subcommand(
        "digest", "Compute a cryptographic digest of events");
    add_common_options(digest, digest_var.common_options, "digest");
    add_seqno_range_options(digest, digest_var.common_options);
    digest->add_flag(
        "-T,--no-time",
        digest_var.erase_timestamps,
        "Set the epoch nanosecond timestamps to zero");
    digest->add_flag(
        "-P,--no-payload-offset",
        digest_var.erase_payload_offset,
        "Set the payload buffer offset to zero");
    digest
        ->add_option(
            "-C,--erase-content-ext-mask",
            digest_var.erase_content_ext_mask,
            "Erase user fields bitmask")
        ->type_name("<hex-mask>")
        ->check(CLI::Range(0, 15));
    digest->immediate_callback();
    digest->callback([&digest_var, &digest_commands] {
        digest_commands.push_back(digest_var);
        digest_var = {};
    });

    /*
     * dump subcommand
     */

    CLI::App *const dump = cli.add_subcommand("dump", "Dump events to a file");
    add_common_options(dump, dump_var.common_options, "dump");
    add_seqno_range_options(dump, dump_var.common_options);
    dump->add_flag("-H,--hex", dump_var.hexdump, "Hexdump event payloads");
    dump->add_flag("-d,--decode", dump_var.decode, "Decode event payloads");
    dump->add_flag(
        "-c,--content-ext",
        dump_var.always_dump_content_ext,
        "Force dump raw content extension values");
    dump->immediate_callback();
    dump->callback([&dump_var, &dump_commands] {
        dump_commands.push_back(dump_var);
        dump_var = {};
    });
    dump->footer(
        R"(The dump subcommand configures the options for formatting events to an output
file. This subcommand can be repeated, and each instance of it will configure a
a new dump operation. This can be used to dump multiple event rings into one
output stream.

If the ---thread or --output option is missing, their values are taken from the
last instance of the dump subcommand to specify them. This behavior (or
explicitly specifying the same thread name) can cause multiple dump operations
to occur on the same thread. In this case, the events are dumped in a
round-robin fashion.

If no subcommand instance specifies an --output option, stdout will be used.)");

    /*
     * execstat subcommand
     */

    CLI::App *const execstat =
        cli.add_subcommand("execstat", "Print execution statistics");
    execstat->alias("xs");
    execstat_var.common_options.event_source_spec =
        g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_EXEC];
    add_common_options(execstat, execstat_var.common_options, "execstat");
    add_tui_mode_option(execstat, execstat_var.tui_mode);
    execstat->immediate_callback();
    execstat->callback([&execstat_var, &execstat_commands] {
        execstat_commands.push_back(execstat_var);
        execstat_var = {};
        execstat_var.common_options.event_source_spec =
            g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_EXEC];
    });

    /*
     * headstat subcommand
     */

    CLI::App *const headstat =
        cli.add_subcommand("headstat", "Print live event ring file statistics");
    headstat->alias("hs");
    add_common_options(headstat, headstat_command.common_options, "headstat");
    headstat->remove_option(headstat->get_option("--source"));
    headstat->add_option("file", headstat_command.inputs, "Event ring fil")
        ->type_name("<event-ring-file>");
    headstat
        ->add_option(
            "-s,--stat",
            headstat_command.stats_interval,
            "Print statistics update after this period")
        ->type_name("<seconds>")
        ->check(CLI::Range(1, 600))
        ->required();
    headstat->get_option("--output")
        ->description("Output file, stdout if not specified");
    headstat->add_flag(
        "-Z,--no-zeros",
        headstat_command.discard_zero_samples,
        "Remove samples when no events are recorded");
    add_tui_mode_option(headstat, headstat_command.tui_mode);
    headstat->footer(
        R"(The event ring file header will be statistically sampled at the
specified rate, to produce a sample distribution for events/second and the
MiB/s payload consumption rate.)");

    /*
     * info subcommand
     */

    CLI::App *const info =
        cli.add_subcommand("info", "Print event source file information");
    add_common_options(info, info_command.common_options, "info");
    info->remove_option(info->get_option("--source"));
    info->remove_option(info->get_option("--thread"));
    info->add_option(
            "source",
            info_command.event_source_specs,
            "Event ring, capture file, archive directory, or --input name")
        ->type_name("<event-source-spec>");
    info->add_flag(
        "--full-section-table",
        info_command.full_evcap_section_table,
        "Print the full section table for evcap files");

    /*
     * record subcommand
     */

    CLI::App *const record = cli.add_subcommand(
        "record", "Record events; creates an event capture (evcap) file");
    add_common_options(record, record_var.common_options, "record");
    add_seqno_range_options(record, record_var.common_options);
    record
        ->add_option(
            "-z,--event-zstd-level",
            record_var.event_zstd_level,
            "zstd compression level for event bundle section")
        ->type_name("<zstd-level>")
        ->check(CLI::Range(0, 22));
    record
        ->add_option(
            "-i,--index-zstd-level",
            record_var.seqno_zstd_level,
            "zstd compression level for sequence number index")
        ->type_name("<zstd-level>")
        ->check(CLI::Range(0, 22));
    record
        ->add_option(
            "--vbuf-segment-shift",
            record_var.vbuf_segment_shift,
            "vbuf segment size shift (power of 2)")
        ->default_val(26)
        ->capture_default_str()
        ->type_name("<vbuf-size-shift>")
        ->check(CLI::Range(12, 32));
    record->add_flag(
        "--no-seqno-index",
        record_var.no_seqno_index,
        "Disable the sequence number index");
    record->immediate_callback();
    record->callback([&record_var, &record_commands] {
        record_commands.push_back(record_var);
        record_var = {};
    });

    /*
     * recordexec subcommand
     */

    CLI::App *const recordexec = cli.add_subcommand(
        "recordexec", "Record execution events with in a block-aware format");
    recordexec->alias("rex");
    recordexec_var.common_options.event_source_spec =
        g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_EXEC];
    add_common_options(recordexec, recordexec_var.common_options, "recordexec");
    add_seqno_range_options(recordexec, recordexec_var.common_options);
    recordexec->get_option("--output")->required();
    recordexec
        ->add_option(
            "-f,--format",
            recordexec_var.block_format,
            "block recording format")
        ->required()
        ->default_val(BlockRecordFormat::Archive)
        ->type_name("<block-format>")
        ->transform(CLI::CheckedTransformer(
            std::unordered_map<std::string, BlockRecordFormat>{
                {"archive", BlockRecordFormat::Archive},
                {"packed", BlockRecordFormat::Packed}},
            CLI::ignore_case));
    recordexec
        ->add_option(
            "-z,--event-zstd-level",
            recordexec_var.event_zstd_level,
            "zstd compression level for finalized block sections")
        ->type_name("<zstd-level>")
        ->check(CLI::Range(0, 22));
    recordexec
        ->add_option(
            "-i,--index-zstd-level",
            recordexec_var.seqno_zstd_level,
            "zstd compression level for sequence number index")
        ->type_name("<zstd-level>")
        ->check(CLI::Range(0, 22));
    recordexec
        ->add_option(
            "--vbuf-segment-shift",
            recordexec_var.vbuf_segment_shift,
            "vbuf segment size shift (power of 2)")
        ->default_val(26)
        ->capture_default_str()
        ->type_name("<vbuf-size-shift>")
        ->check(CLI::Range(12, 32));
    recordexec
        ->add_option(
            "--pack-max-sections-shift",
            recordexec_var.pack_max_sections_shift,
            "maximum number of evcap sections shift (power of 2)")
        ->default_val(9)
        ->capture_default_str()
        ->type_name("<max-sections-shift>")
        ->check(CLI::Range(0, 32));
    recordexec->immediate_callback();
    recordexec->callback([&recordexec_var, &recordexec_commands] {
        recordexec_commands.push_back(recordexec_var);
        recordexec_var = {};
        recordexec_var.common_options.event_source_spec =
            g_monad_event_content_type_names[MONAD_EVENT_CONTENT_TYPE_EXEC];
    });

    /*
     * sectiondump subcommand
     */

    CLI::App *const sectiondump = cli.add_subcommand(
        "sectiondump", "Low-level dump of evcap file sections");
    sectiondump->alias("secdump");
    add_common_options(
        sectiondump, sectiondump_command.common_options, "sectiondump");
    sectiondump->remove_option(sectiondump->get_option("--source"));
    sectiondump->remove_option(sectiondump->get_option("--thread"));
    sectiondump
        ->add_option(
            "file",
            sectiondump_command.common_options.event_source_spec,
            "Event capture file")
        ->type_name("<evcap-file>");
    sectiondump
        ->add_option(
            "-j,--section", sectiondump_command.sections, "Section index")
        ->type_name("<section-spec>");
    sectiondump->add_flag(
        "-d,--digest",
        sectiondump_command.digest,
        "Compute crypographic digest of section contents");
    sectiondump->add_flag(
        "-H,--hexdump",
        sectiondump_command.hexdump,
        "Hexdump section contents");
    sectiondump->add_flag(
        "--no-decompress",
        sectiondump_command.no_decompress,
        "Do not decompress section content before dumping");

    /*
     * snapshot subcommand
     */

    CLI::App *const snapshot =
        cli.add_subcommand("snapshot", "Create snapshot of event ring");
    snapshot->alias("snap");
    add_common_options(snapshot, snapshot_var.common_options, "snapshot");
    add_seqno_range_options(snapshot, snapshot_var.common_options);
    snapshot
        ->add_option(
            "--vbuf-segment-shift",
            snapshot_var.vbuf_segment_shift,
            "Max payload shift (power of 2)")
        ->default_val(26)
        ->capture_default_str()
        ->type_name("<payload-size-shift>")
        ->check(CLI::Range(22, 32));
    snapshot->add_flag(
        "-k,--kill",
        snapshot_var.kill_at_end,
        "Set SIGINT signal to processes when terminated");
    snapshot->add_flag(
        "-T,--no-time",
        snapshot_var.erase_timestamps,
        "Set the epoch nanosecond timestamps to zero");
    snapshot->immediate_callback();
    snapshot->callback([&snapshot_var, &snapshot_commands] {
        snapshot_commands.push_back(snapshot_var);
        snapshot_var = {};
    });
    snapshot->footer(
        R"(The snapshot subcommand configures the options for writing events to a
snapshot event ring file. A snapshot event ring file is just a copy of a
regular event ring file, but is large enough to hold many events number without
wrapping around and over-writing earlier ones. This is used to create test
case data, or to re-create replay inputs. Typically the user runs zstd to
compress the output ring file, e.g.:

    monad-event-cli snap -sexec -o- -e 100000 | zstd -19 > /tmp/snapshot.zst

If the user does not specify an ending sequence number describing when to
terminate the snapshot, it must be terminated manually by sending SIGINT to
monad-event-cli, usually via the Ctrl^C control character entered into the
controlling terminal.

In that case, the typical way of running the above command would require
setsid(1) to be used for the later pipeline stage so it is not interrupted
along with the process group leader (which is monad-event-cli), e.g.:

    monad-event-cli snap -sexec -o- | sedsid zstd -19 > /tmp/snapshot.zst

The threading model behaves the same as the dump command.)");

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(cli.exit(e));
    }
    catch (CLI::ParseError const &e) {
        std::exit(cli.exit(e));
    }

    CommandBuilder builder{input_specs, force_live_specs};

    // Stream commands
    for (BlockStatCommandOptions const &o : blockstat_commands) {
        builder.build_blockstat_command(o);
    }
    for (DigestCommandOptions const &o : digest_commands) {
        builder.build_digest_command(o);
    }
    for (DumpCommandOptions const &o : dump_commands) {
        builder.build_dump_command(o);
    }
    for (ExecStatCommandOptions const &o : execstat_commands) {
        builder.build_execstat_command(o);
    }
    for (RecordCommandOptions const &o : record_commands) {
        builder.build_record_command(o);
    }
    for (RecordExecCommandOptions const &o : recordexec_commands) {
        builder.build_recordexec_command(o);
    }
    for (SnapshotCommandOptions const &o : snapshot_commands) {
        builder.build_snapshot_command(o);
    }

    // Miscellaneous commands
    if (headstat->count() > 0) {
        builder.build_headstat_command(headstat_command);
    }
    if (info->count() > 0) {
        builder.build_info_command(info_command);
    }
    if (sectiondump->count() > 0) {
        builder.build_sectiondump_command(sectiondump_command);
    }

    return run_commands(builder.finish());
}
