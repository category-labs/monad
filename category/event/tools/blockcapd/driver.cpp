#include <algorithm>
#include <charconv>
#include <concepts>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <functional>
#include <print>
#include <ranges>

#include <err.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <linux/limits.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sysexits.h>
#include <syslog.h>
#include <unistd.h>

#include <category/core/assert.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/event/blockcap.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

// TODO: do better than glibc backtrace
#include <execinfo.h>

#include "blockcapd.hpp"

namespace fs = std::filesystem;

extern char const *__progname;
std::sig_atomic_t g_exit_signaled;
std::function<void(LogMessage const &)> g_log_writter;

namespace
{

void usage(std::FILE *out)
{
    std::println(out, "usage: {} [options] <block-archive-dir>", __progname);
}

[[noreturn]] void help()
{
    usage(stdout);
    std::println(
        stdout,
        R"(
block capture daemon

This program connects to an execution event ring and populates the
local finalized block archive with the data it observes.

Options:
  -h | --help                    print this message
  -e | --event-ring-path <path>  alternate path to execution event ring
  -t | --timeout <seconds>       number of seconds to wait for event ring
                                     file to be created before exiting
                                     [default: <none> (waits forever)]
  -f | --finalized-block <#>     rewind to capture events after last
                                     finalized block number
  -s | --seqno <#>               set the iterator to this sequence number
  -e | --event-zstd-level <#>    event section zstd compression level
                                     [default: {}]
  -i | --index-zstd-level <#>    sequence number index zstd compression
                                     level [default: {}]
  --vbuf-segment-shift <#>       vbuf allocator segment size (specified
                                     as power-of-2 shift) [default: {}]
  --force-live                   force read from zombie event rings (to
                                     debug this program w/ snapshots)

Positional arguments:
  <block-archive-dir>    path of the local block archive directory)",
        DefaultZStdCompressionLevel,
        DefaultZStdCompressionLevel,
        DefaultVBufSegmentShift);
    std::exit(0);
}

enum LongOnlyOption : int
{
    LO_VBUF_SEGMENT_SHIFT = 256,
    LO_FORCE_LIVE,
};

struct option const longopts[] = {
    {"help", no_argument, nullptr, 'h'},
    {"timeout", required_argument, nullptr, 't'},
    {"event-ring-path", required_argument, nullptr, 'e'},
    {"finalized-block", required_argument, nullptr, 'f'},
    {"seqno", required_argument, nullptr, 's'},
    {"event-zstd-level", required_argument, nullptr, 'z'},
    {"index-zstd-level", required_argument, nullptr, 'i'},
    {"vbuf-segment-shift", required_argument, nullptr, LO_VBUF_SEGMENT_SHIFT},
    {"force-live", no_argument, nullptr, LO_FORCE_LIVE},
    {}};

template <std::integral I>
void try_parse_integer_token(char const *token, I &i)
{
    char const *const end = token + std::strlen(token);
    auto const [ptr, ec] = std::from_chars(token, end, i);
    if (ptr != end) {
        errno = EINVAL;
        err(EX_USAGE, "could not parse %s as an integer", token);
    }
    if (auto const e = static_cast<int>(ec)) {
        errno = e;
        err(EX_USAGE, "could not parse %s as an integer", token);
    }
}

template <std::integral I>
void check_range(I value, int option_val, I lower, I upper)
{
    if (value < lower || value > upper) {
        auto const i = std::ranges::find(longopts, option_val, &option::val);
        MONAD_ASSERT(i != std::ranges::end(longopts));
        std::println(
            stderr,
            "{}: option --{} outside of allowed range [{}, {}]",
            __progname,
            i->name,
            lower,
            upper);
        std::exit(EX_CONFIG);
    }
}

int parse_options(int argc, char **argv, BlockCapOptions *options)
{
    int ch;

    while ((ch = getopt_long(argc, argv, "he:t:f:s:z:i:", longopts, nullptr)) !=
           -1) {
        switch (ch) {
        case 'h':
            help();

        case 'e':
            options->exec_ring_path = optarg;
            break;

        case 't':
            try_parse_integer_token(optarg, options->connect_timeout.emplace());
            break;

        case 'f':
            try_parse_integer_token(
                optarg, options->seek_finalized_block.emplace());
            break;

        case 's':
            try_parse_integer_token(optarg, options->seek_seqno.emplace());
            break;

        case 'z':
            try_parse_integer_token(
                optarg, options->event_zstd_level.emplace());
            break;

        case 'i':
            try_parse_integer_token(
                optarg, options->seqno_index_zstd_level.emplace());
            break;

        case LO_VBUF_SEGMENT_SHIFT:
            try_parse_integer_token(
                optarg, options->vbuf_segment_shift.emplace());
            break;

        case LO_FORCE_LIVE:
            options->force_live = true;
            break;

        default:
            usage(stderr);
            std::exit(EX_USAGE);
        }
    }

    return optind;
}

void validate_options(BlockCapOptions *options)
{
    // --event-zstd-level
    if (options->event_zstd_level) {
        check_range((unsigned)*options->event_zstd_level, 'z', 0U, 22U);
    }
    else {
        options->event_zstd_level = DefaultZStdCompressionLevel;
    }

    // --index-zstd-level
    if (options->seqno_index_zstd_level) {
        check_range((unsigned)*options->seqno_index_zstd_level, 'i', 0U, 22U);
    }
    else {
        options->seqno_index_zstd_level = DefaultZStdCompressionLevel;
    }

    // --vbuf-segment-size
    if (options->vbuf_segment_shift) {
        check_range(
            (unsigned)*options->vbuf_segment_shift,
            LO_VBUF_SEGMENT_SHIFT,
            1u,
            30u);
    }
    else {
        options->vbuf_segment_shift = DefaultVBufSegmentShift;
    }

    if (options->seek_finalized_block && options->seek_seqno) {
        errx(EX_USAGE, "cannot specify both --finalized-block and --seqno");
    }
}

monad_bcap_archive *open_block_archive(char const *path)
{
    monad_bcap_archive *block_archive;

    if (mkdir(path, DirCreateMode) == -1 && errno != EEXIST) {
        err(EX_OSERR, "mkdir of block archive directory `%s` failed", path);
    }
    int const fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd == -1) {
        err(EX_OSERR, "open of block archive directory `%s` failed", path);
    }
    if (monad_bcap_archive_open(&block_archive, fd, path) != 0) {
        errx(
            EX_SOFTWARE,
            "bcap library error -- %s",
            monad_bcap_get_last_error());
    }
    (void)close(fd);
    return block_archive;
}

uint64_t *mmap_last_finalized_block_file(char const *block_archive_path)
{
    struct stat file_stat;
    fs::path const file_path =
        fs::path{block_archive_path} / "last_finalized_block";
    int const fd =
        open(file_path.c_str(), O_CREAT | O_RDWR | O_CLOEXEC, FileCreateMode);
    if (fd == -1) {
        err(EX_OSERR, "open of `%s` failed", file_path.c_str());
    }
    if (flock(fd, LOCK_EX | LOCK_NB) == -1) {
        if (errno != EWOULDBLOCK) {
            err(EX_OSERR, "flock of `%s` failed", file_path.c_str());
        }
        monad_event_flock_info fl_info;
        size_t flock_count = 1;
        if (monad_event_ring_query_flocks(fd, &fl_info, &flock_count) != 0) {
            errx(
                EX_UNAVAILABLE,
                "could not flock `%s` because of unknown process",
                file_path.c_str());
        }
        errx(
            EX_UNAVAILABLE,
            "could not flock `%s` because of %d placed by %d",
            file_path.c_str(),
            fl_info.lock,
            fl_info.pid);
    }
    if (fstat(fd, &file_stat) == -1) {
        err(EX_OSERR, "fstat fo `%s` failed", file_path.c_str());
    }
    if (file_stat.st_size == 0 && ftruncate(fd, sizeof(uint64_t)) == -1) {
        err(EX_OSERR,
            "ftruncate of `%s` to size %zu failed",
            file_path.c_str(),
            sizeof(uint64_t));
    }
    uint64_t *const last_finalized = reinterpret_cast<uint64_t *>(mmap(
        nullptr, sizeof(uint64_t), PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0));
    if (last_finalized == MAP_FAILED) {
        err(EX_OSERR, "mmap of `%s` failed", file_path.c_str());
    }
    BCD_INFO_NS(
        "last finalized block {} read from `{}`",
        *last_finalized,
        file_path.c_str());
    return last_finalized;
}

void exit_signal_handler(int)
{
    g_exit_signaled = 1;
}

char const *describe(LogPriority p)
{
    using enum LogPriority;
    switch (p) {
    case Emergency:
        return "EMERG";
    case Alert:
        return "ALERT";
    case Critical:
        return "CRIT";
    case Error:
        return "ERR";
    case Warning:
        return "WARN";
    case Notice:
        return "NOTE";
    case Info:
        return "INFO";
    case Debug:
        return "DEBUG";
    default:
        return "?";
    }
}

// Could also call sd_journal_print_with_location here instead
void default_log_writter(LogMessage const &m)
{
    std::FILE *const log_file =
        m.priority <= LogPriority::Notice ? stderr : stdout;
    std::print(log_file, "[{:5}]: {}", describe(m.priority), m.message);
    if (m.source_location) {
        std::string const file =
            fs::path{m.source_location->file_name()}.filename();
        std::print(
            log_file,
            " @ {}:{}:{} -- {}",
            file,
            m.source_location->line(),
            m.source_location->column(),
            m.source_location->function_name());
    }
    std::println(log_file);
    if (log_file == stdout) {
        std::fflush(log_file);
    }
}

} // End of anonymous namespace

extern "C" void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool print_async_unsafe_info)
{
    int const n_frames =
        backtrace((void **)buffer, (int)(size / sizeof(void *)));
    backtrace_symbols_fd((void *const *)buffer, n_frames, fd);
    (void)indent, (void)print_async_unsafe_info;
}

int main(int argc, char **argv)
{
    g_log_writter = default_log_writter;
    BlockCapOptions options{};
    options.exec_ring_path = MONAD_EVENT_DEFAULT_EXEC_FILE_NAME;

    int const pos_arg_idx = parse_options(argc, argv, &options);
    if (argc - pos_arg_idx != 1) {
        std::println(
            stderr, "{}: expected <block-archive-dir> argument", __progname);
        usage(stderr);
        return EX_USAGE;
    }
    validate_options(&options);

    monad_bcap_archive *const block_archive =
        open_block_archive(argv[pos_arg_idx]);

    uint64_t *const last_finalized =
        mmap_last_finalized_block_file(argv[pos_arg_idx]);

    char resolved_exec_ring_path[PATH_MAX];
    if (monad_event_resolve_ring_file(
            MONAD_EVENT_DEFAULT_HUGETLBFS,
            options.exec_ring_path.c_str(),
            resolved_exec_ring_path,
            sizeof resolved_exec_ring_path) != 0) {
        errx(
            EX_SOFTWARE,
            "event ring library error -- %s",
            monad_event_ring_get_last_error());
    }
    if (resolved_exec_ring_path != options.exec_ring_path) {
        BCD_INFO_NS(
            "event ring input `{}` resolved to path `{}`",
            options.exec_ring_path,
            resolved_exec_ring_path);
        options.exec_ring_path = resolved_exec_ring_path;
    }

    if (isatty(STDIN_FILENO)) {
        // When stdin is connected to a terminal, we're running interactively
        std::signal(SIGINT, exit_signal_handler);
    }
    std::signal(SIGTERM, exit_signal_handler);
    capture_blocks(&options, block_archive, last_finalized);
    monad_bcap_archive_close(block_archive);
    (void)munmap(last_finalized, sizeof(uint64_t));
    return 0;
}
