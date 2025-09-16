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

/**
 * @file
 *
 * Historical event recovery example - this small CLI application serves as a
 * demo of how to recover execution events that we missed for some reason
 * (our processing program crashed, the execution daemon crashed, etc.) It
 * relies on replaying a local copy of any blocks that were not processed.
 *
 * The local blocks are either already present on the host (written by a local
 * `monad-blockcapd` daemon) or they are downloaded from a cloud archive. This
 * program does not care how the blocks were recorded. If they are missing,
 * it invokes an external process to download any missing blocks to disk.
 *
 * It is up to this external process to ensure the requested blocks are
 * populated in the local block directory structure, which could include
 * downloading the missing data from a remote archive.
 */

#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <err.h>
#include <fcntl.h>
#include <getopt.h>
#include <poll.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sysexits.h>
#include <time.h>
#include <unistd.h>

#if defined(__linux__)
    #include <linux/limits.h>
    #include <syscall.h>
#else
    #define PATH_MAX 4096
#endif

#include <category/core/event/evcap_file.h>
#include <category/core/event/evcap_reader.h>
#include <category/core/event/event_def.h>
#include <category/core/event/event_metadata.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_iter.h>
#include <category/core/event/event_ring_util.h>
#include <category/core/event/event_source.h>
#include <category/execution/ethereum/event/blockcap.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_iter_help.h>

constexpr char DEFAULT_FETCH_COMMAND[] = "fetch-exec-events-blocks";
extern char const *__progname;

static void usage(FILE *out)
{
    fprintf(
        out,
        "usage: %s [-hv] [-f <cmd>] [-r <ring>] <block-dir> <last-finalized>\n",
        __progname);
}

// clang-format off

[[noreturn]] static void help()
{
    usage(stdout);
    fprintf(stdout,
"\n"
"block history recovery example program\n"
"\n"
"Options:\n"
"  -h | --help              print this message\n"
"  -f | --fetch <cmd>       name of the block fetch command [default %s]\n"
"  -r | --ring <file-name>  event ring file name [default: %s]\n"
"  -v | --verbose           be more verbose; can be repeated\n"
"\n"
"Positional arguments:\n"
"  <block-dir>        path to the directory containing finalized blocks;\n"
"                       this may have an incomplete local history, in\n"
"                       which case it will be populated using the block\n"
"                       fetch command\n"
"  <last-finalized>   the last finalized block number which the user\n"
"                       has definitely seen; we will replay every block\n"
"                       after this, then switch to the live event ring\n",
    DEFAULT_FETCH_COMMAND,
    MONAD_EVENT_DEFAULT_EXEC_FILE_NAME);
    exit(0);
}

struct option const longopts[] = {
    {"help", no_argument, nullptr, 'h'},
    {"fetch", required_argument, nullptr, 'f'},
    {"ring", required_argument, nullptr, 'r'},
    {"verbose", no_argument, nullptr, 'v'},
    {}
};

// clang-format on

// Half open range (block_start, block_end] representing a range of blocks
// we need to fetch from the local archive. The range is half open on the
// left side because everything is written in terms of "what is the last block
// that we have definitely already seen?" (and so does not need to be fetched)
// rather than "what is the first block that is unseen?" (because this is
// potentially nothing, if we're caught up)
typedef struct block_range
{
    uint64_t block_start;
    uint64_t block_end;
} block_range_t;

// Program configuration parsed from the command line
struct config
{
    char const *fetch_command;
    char const *event_ring_path;
    char const *block_dir_path;
    uint64_t last_finalized_block;
    unsigned verbose;
};

// Parses argv[] into a valid config structure, or exits
static struct config parse_arguments(int argc, char **argv)
{
    int ch;
    struct config cfg = {
        .fetch_command = DEFAULT_FETCH_COMMAND,
        .event_ring_path = MONAD_EVENT_DEFAULT_EXEC_FILE_NAME,
        .block_dir_path = nullptr,
        .last_finalized_block = 0,
        .verbose = 0,
    };

    while ((ch = getopt_long(argc, argv, "hf:r:v", longopts, nullptr)) != -1) {
        switch (ch) {
        case 'h':
            help();

        case 'f':
            cfg.fetch_command = optarg;
            break;

        case 'r':
            cfg.event_ring_path = optarg;
            break;

        case 'v':
            ++cfg.verbose;
            break;

        default:
            usage(stderr);
            exit(EX_USAGE);
        }
    }

    if (argc - optind != 2) {
        usage(stderr);
        exit(EX_USAGE);
    }

    // <block-dir-path> positional argument
    cfg.block_dir_path = argv[optind];

    // <last-finalized> positional argument
    char *strtoul_out;
    errno = 0;
    cfg.last_finalized_block = strtoul(argv[optind + 1], &strtoul_out, 0);
    if (errno != 0 || *strtoul_out != '\0') {
        err(EX_USAGE,
            "invalid <last-finalized-block> parameter `%s`",
            argv[optind + 1]);
    }

    return cfg;
}

static sig_atomic_t g_should_stop;

static void handle_signal(int)
{
    g_should_stop = 1;
}

// Check if the process referred to by the pidfd has exited or not
static bool process_has_exited(int pidfd)
{
    if (pidfd == -1) {
        // pidfd being -1 means "disable the detection feature"
        return false;
    }
    struct pollfd pfd = {.fd = pidfd, .events = POLLIN};
    return poll(&pfd, 1, 0) == -1 || (pfd.revents & POLLIN) == POLLIN;
}

// Return the directory that this example program is running from; our
// executable's directory is one place where we'll search for the block fetch
// program
static char *get_exec_dir_name()
{
    char path[PATH_MAX];
    ssize_t const n_read = readlink("/proc/self/exe", path, sizeof path);
    if (n_read == -1) {
        return nullptr;
    }
    if (n_read == sizeof path) {
        errno = ENAMETOOLONG;
        return nullptr;
    }
    path[n_read] = '\0';
    return strdup(path);
}

// Given a command for the "block fetch" program, resolve it to an absolute
// path of a program to run; returns nullptr if no such program is found
static char *resolve_fetch_command(char const *cmd, unsigned verbose)
{
    // Search order: $PATH, current working directory, and the directory where
    // the current executable is located
    char *(*const path_resolvers[])() = {
        get_current_dir_name, get_exec_dir_name};

    if (strchr(cmd, '/') != nullptr) {
        // General UNIX shell style is we only do complex command lookup when
        // passed a "pure" command name; this command name has a '/' so it is
        // always resolved relative to the current working directory
        if (verbose > 1) {
            fprintf(
                stderr,
                "%s: fetch cmd `%s` will resolve relative to $PWD\n",
                __progname,
                cmd);
        }
        return realpath(cmd, nullptr);
    }

    // Seed the path search list with the PATH environment variable
    char const *const path_env = getenv("PATH");
    char *path_search = strdup(path_env != nullptr ? path_env : "");
    if (path_search == nullptr) {
        err(EX_OSERR, "strdup failed");
    }

    // Add in current working directory and executable directory
    for (size_t fn = 0; fn < 2; ++fn) {
        char *const extra_dir_name = path_resolvers[fn]();
        if (extra_dir_name == nullptr) {
            err(EX_OSERR, "get_current_dir_name failed");
        }
        // Grow the path buffer to hold this new directory, then append
        // ":<new-dir>"
        path_search = realloc(
            path_search, strlen(path_search) + strlen(extra_dir_name) + 1);
        if (path_search == nullptr) {
            err(EX_OSERR, "realloc failed");
        }
        sprintf(path_search + strlen(path_search), ":%s", extra_dir_name);
        free(extra_dir_name);
    }

    void *const orig_path_search = path_search; // for free(3)
    char const *next_path;
    char *fetch_command = nullptr;
    char access_buf[PATH_MAX];

    // For each search path entry, check if <path-candidate>/cmd is an
    // executable file, and stop as soon as we find something that works
    while ((next_path = strsep(&path_search, ":"))) {
        int const buf_size =
            snprintf(access_buf, sizeof access_buf, "%s/%s", next_path, cmd);
        if (buf_size < 0 || (size_t)buf_size >= sizeof access_buf) {
            errx(
                EX_SOFTWARE,
                "candidate fetch command %s/%s too large",
                next_path,
                cmd);
        }
        if (verbose > 1) {
            fprintf(
                stderr,
                "%s: checking fetch candidate %s\n",
                __progname,
                access_buf);
        }
        if (access(access_buf, X_OK) == 0) {
            fetch_command = realpath(access_buf, nullptr);
            if (verbose > 0) {
                fprintf(
                    stderr,
                    "%s: fetch candidate %s selected\n",
                    __progname,
                    fetch_command);
            }
            break;
        }
    }

    free(orig_path_search);
    return fetch_command;
}

// Run the block fetch command to download the given missing block ranges
// in the local finalized block archive directory; most of the time, we hope
// that this does nothing because the files already exist locally. If there are
// missing block files, it will download them from a remote archive. Either way,
// the assumption is that once this function returns, any block in that range
// can be opened without an ENOENT error
static void fetch_missing_block_ranges(
    char const *fetch_command, char const *block_dir_path,
    struct monad_bcap_block_range_list *missing_ranges, bool verbose)
{
    char **argv;
    size_t argc;
    size_t arg_size;
    siginfo_t exit_info;
    struct monad_bcap_block_range *missing;

    argv = (char **)malloc((3 + missing_ranges->num_segments) * sizeof(char *));
    if (argv == nullptr) {
        err(EX_OSERR, "calloc of execv argv array failed");
    }
    argc = 0;
    arg_size = 0;
    argv[argc++] = strdup(fetch_command);
    argv[argc++] = strdup(block_dir_path);
    TAILQ_FOREACH(missing, &missing_ranges->head, next)
    {
        if (asprintf(&argv[argc++], "%lu-%lu", missing->min, missing->max) ==
            -1) {
            err(EX_OSERR, "asprintf failed");
        }
    }
    argv[argc] = nullptr;
    for (size_t i = 0; i < argc; ++i) {
        if (argv[i] == nullptr) {
            errx(EX_OSERR, "memory allocation for argument %zu failed", i);
        }
        arg_size += strlen(argv[i]);
    }
    if (arg_size > ARG_MAX) {
        errx(
            EX_SOFTWARE,
            "argv for block fetch program overflow: %zu",
            arg_size);
    }

    if (verbose) {
        fprintf(stderr, "%s: running fetch command:", __progname);
        for (size_t i = 0; i < argc; ++i) {
            fprintf(stderr, " %s", argv[i]);
        }
        fprintf(stderr, "\n");
    }
    pid_t const child_pid = fork();
    if (child_pid == -1) {
        err(EX_OSERR, "fork failed");
    }
    if (child_pid == 0) {
        // We are the child; exec(2) the fetch program
        if (execv(fetch_command, argv) == -1) {
            err(EX_OSERR, "execl(2) of %s failed", fetch_command);
        }
    }
    for (size_t i = 0; i < argc; ++i) {
        free(argv[i]);
    }
    free((void *)argv);

    // We're the parent; wait for the child. In a real program we wouldn't
    // wait forever, since the program could hang and would need to be killed
    // and restarted. We would need to have some kind of policy, e.g., to
    // decide if it is taking too long / not making progress. In this toy
    // example, we just wait forever
    if (waitid(P_PID, (id_t)child_pid, &exit_info, WEXITED) == -1) {
        err(EX_OSERR, "waitid failed");
    }
    if (exit_info.si_code == CLD_EXITED && exit_info.si_status == 0) {
        return; // child called exit(SUCCESS);
    }

    // Child terminated unexpectedly
    switch (exit_info.si_code) {
    case CLD_EXITED:
        errx(
            exit_info.si_status,
            "%s: fetch command %s exited with status %d",
            __progname,
            fetch_command,
            exit_info.si_status);

    case CLD_DUMPED:
        [[fallthrough]];
    case CLD_KILLED:
        errx(
            EX_SOFTWARE,
            "%s: fetch command %s was killed by signal %d%s",
            __progname,
            fetch_command,
            exit_info.si_status,
            exit_info.si_code == CLD_DUMPED ? " [dump]" : "");

    default:
        fprintf(stderr, "unexpect siginfo_t code: %d", exit_info.si_code);
        abort();
    }
}

// Wait for the live event ring file be (re-)created, then mmap in into our
// address space
static int open_event_ring(
    char const *event_ring_path, struct monad_event_ring *exec_ring, int *pidfd)
{
    int rc;
    int ring_fd;
    pid_t writer_pid;

    *pidfd = -1;

    // First, remove the previous mapping; initially this does nothing
    monad_event_ring_unmap(exec_ring);
    rc = monad_event_ring_wait_for_excl_writer(
        event_ring_path,
        nullptr,
        nullptr,
        O_RDONLY | O_CLOEXEC,
        &ring_fd,
        &writer_pid);
    if (rc == EINTR) {
        return EINTR;
    }
    if (rc != 0) {
        err(EX_UNAVAILABLE,
            "event library error -- %s",
            monad_event_ring_get_last_error());
    }
    if (monad_event_ring_mmap(
            exec_ring, PROT_READ, MAP_HUGETLB, ring_fd, 0, event_ring_path) !=
        0) {
        goto EventRingError;
    }

    if (monad_event_ring_check_content_type(
            exec_ring,
            MONAD_EVENT_CONTENT_TYPE_EXEC,
            g_monad_exec_event_schema_hash) != 0) {
        goto EventRingError;
    }

#if defined(__linux__)
    *pidfd = (int)syscall(SYS_pidfd_open, writer_pid, 0);
    if (*pidfd == -1) {
        if (errno == ESRCH) {
            monad_event_ring_unmap(exec_ring);
            return ESRCH; // This was a race, so keep trying
        }
        err(EX_OSERR, "pidfd_open of writer pid %d failed", writer_pid);
    }
#endif

    (void)close(ring_fd);
    struct monad_event_ring_iter iter;
    if (monad_event_ring_init_iterator(exec_ring, &iter) != 0) {
        goto EventRingError;
    }

    return 0;

EventRingError:
    errx(
        EX_SOFTWARE,
        "event library error -- %s",
        monad_event_ring_get_last_error());
}

// Given the last finalized block number we know about, detect the most recently
// produced finalized block in the live event ring and compute the half-open
// range of all the blocks we have not seen
static block_range_t compute_unseen_block_range(
    uint64_t last_finalized_block, struct monad_event_ring const *event_ring,
    int pidfd)
{
    block_range_t r = {.block_start = last_finalized_block};
    unsigned wait_count = 0;

    while (!monad_exec_get_most_recent_finalized(event_ring, &r.block_end)) {
        // Unable to find the most recent BLOCK_FINALIZED event with full
        // in-ring history; this means that execution has been restarted
        // recently, and there is not yet a single finalized block (and its
        // corresponding proposal) in the live ring. We'll wait a few seconds
        // for one to appear before giving up and deciding that something has
        // gone wrong enough that it's not going to happen.
        constexpr unsigned MAX_WAIT_COUNT = 15;
        if (wait_count++ > MAX_WAIT_COUNT ||
            (pidfd != -1 && process_has_exited(pidfd))) {
            errx(
                EX_UNAVAILABLE,
                "execution detected dead after waiting %u seconds",
                wait_count - 1);
        }
        sleep(1);
    }

    if (r.block_end < r.block_start) {
        errx(
            EX_USAGE,
            "user input claimed last finalized block was %lu but "
            "this block was not seen yet (current finalization is "
            "%lu)",
            r.block_start,
            r.block_end);
    }

    return r;
}

// One of the things this example is trying to show is that if you write your
// software in terms of some processing function `f` (where you call
// `f(event)` to process the next event) then the basic flow looks like this:
//
// RecoverAgain:
//     while (not caught up) {
//         e = get_next_unseen_event();
//         process_event(e);
//     }
//     /* now we are caught up, switch to the live ring */
//     while (!should_exit) {
//         e = get_next_event_from_live_ring();
//         if (is_gap_detected()) {
//             goto RecoverAgain;
//         }
//         process_event(e);
//     }
//
// In this program, `print_event` is the processing function; we do pass an
// enum telling it whether this is replay or a live event, because for some
// processing it might matter.
//
// There is once sense in which it almost always matters: during replay, we
// only see finalized blocks, and no BLOCK_FINALIZED event will be seen, but
// can be assumed to be implicitly emitted after BLOCK_END.
static void print_event(
    struct monad_evsrc_any const *event_source,
    struct monad_event_descriptor const *event, void const *payload, FILE *out)
{
    // This function is similar to the version in eventwatch.c, except that:
    //
    //   1. It is written in terms of the "event source" (evsrc) API, which
    //      unifies the API of the live event ring iterator and the event
    //      capture iterator
    //
    //   2. It does not print a hexdump afterward, although the comment where
    //      it would print one has some important information
    //
    //   3. After BLOCK_END is encountered when liveness == EVENT_REPLAY,
    //      it prints an implicit finalization notice. This is meant to
    //      capture the fact that during "normal" (live) replay we have
    //      to do the extra work of tracking a proposed block through its
    //      consensus states. We don't do that anyway in this example program,
    //      but most real applications need to. But when we are in
    //      EVENT_REPLAY mode, a special case is trigger where we know it is
    //      implicitly finalized
    enum event_liveness
    {
        EVENT_REPLAY,
        EVENT_LIVE,
    };

    static char time_buf[32];
    static time_t last_second = 0;

    ldiv_t time_parts;
    char event_buf[256];
    char *o = event_buf;

    // We can determine whether this event comes from a live event ring or
    // from a capture file from the evsrc iterator
    enum event_liveness const liveness =
        monad_evsrc_any_get_type(event_source) == MONAD_EVSRC_EVENT_RING
            ? EVENT_LIVE
            : EVENT_REPLAY;

    struct monad_event_metadata const *event_md =
        &g_monad_exec_event_metadata[event->event_type];

    time_parts = ldiv((long)event->record_epoch_nanos, 1'000'000'000L);
    if (time_parts.quot != last_second) {
        // A new second has ticked. Reformat the per-second time buffer.
        struct tm;
        last_second = time_parts.quot;
        strftime(
            time_buf, sizeof time_buf, "%H:%M:%S", localtime(&last_second));
    }

    // Print a summary line of this event
    // <HH:MM::SS.nanos> [R|L] <event-c-name> [<event-type> <event-type-hex>]
    //     SEQ: <sequence-number> LEN: <payload-size>
    //     BUF_OFF: <payload-buffer-offset>
    o += sprintf(
        event_buf,
        "%s.%09ld: %c %s [%hu 0x%hx] SEQ: %lu LEN: %u BUF_OFF: %lu",
        time_buf,
        time_parts.rem,
        liveness == EVENT_REPLAY ? 'R' : 'L',
        event_md->c_name,
        event->event_type,
        event->event_type,
        event->seqno,
        event->payload_size,
        event->payload_buf_offset);
    if (event->content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0) {
        uint64_t block_number;
        if (monad_exec_get_block_number(
                event_source, event, payload, &block_number)) {
            o += sprintf(o, " BLK: %lu", block_number);
        }
        else {
            o += sprintf(o, " BLK: <LOST>");
        }
    }
    if (event->content_ext[MONAD_FLOW_TXN_ID] != 0) {
        o += sprintf(o, " TXN: %lu", event->content_ext[MONAD_FLOW_TXN_ID] - 1);
    }

    // To simplify the example, we don't print a hexdump of the event payload
    // like the eventwatch.c example does. If we did, we would need to address
    // the fact that `payload` may point into either
    //
    //   - event ring shared memory, which can be overwritten ("expire") OR
    //   - event capture memory, which never expires
    //
    // This can be detected by calling the event source iterator function
    // `monad_evsrc_iterator_check_payload`. Alternatively, the caller can
    // opt out of using the zero-copy style, and pin `payload` by calling
    // `monad_event_ring_payload_memcpy` before calling this function.
    o += sprintf(
        o,
        " EXPIRED?: %c",
        monad_evsrc_check_payload(event_source, event) ? 'N' : 'Y');
    (void)payload;

    *o++ = '\n';
    fwrite(event_buf, (size_t)(o - event_buf), 1, out);

    if (event->event_type == MONAD_EXEC_BLOCK_END && liveness == EVENT_REPLAY) {
        fprintf(
            out,
            "%s.%09ld REPLAY OF FINALIZED BLOCK FINISHED\n",
            time_buf,
            time_parts.rem);
    }
}

// The main event loop. This starts out by recovering any blocks that we did
// not see, starting after `last_finalized_block` and continuing up to whatever
// the most recently produced finalized block is according to the live
// execution event data.
//
// After this replays all the unseen events from the history, it switches over
// to the live event ring and consumes real-time events until interrupted by
// Ctrl^C. Should a gap occur, it will switch back into recovery mode. You
// can generate a gap by sending SIGSTOP (usually Ctrl^Z), waiting for the event
// ring to overflow, and then resume the process.
static void event_loop(
    struct config const *cfg, struct monad_event_ring const *event_ring,
    struct monad_bcap_archive *block_archive,
    char const *resolved_fetch_command, int pidfd, FILE *out)
{
    // When the gap between the live event ring and the finalized block archive
    // is this size or smaller, switch to the live event ring
    constexpr unsigned LIVE_RING_BLOCK_THRESHOLD = 10;
    struct monad_event_descriptor live_event;
    struct monad_event_ring_iter ring_iter;
    struct monad_bcap_block_range_list missing_ranges;
    void const *payload;
    int rc;
    uint64_t not_ready_count = 0;
    uint64_t last_finalized_block = cfg->last_finalized_block;

RecoverAgain:
    block_range_t unseen =
        compute_unseen_block_range(last_finalized_block, event_ring, pidfd);

    do {
        // Unseen blocks may already be present in the local archive, or we may
        // need to download them using the fetch program; if the unseen range
        // is non-empty, query the local block archive to compute a list of
        // contiguous missing block ranges
        if (unseen.block_end - unseen.block_start > 0) {
            monad_bcap_block_range_list_init(&missing_ranges);
            rc = monad_bcap_archive_find_missing(
                block_archive,
                unseen.block_start + 1,
                unseen.block_end,
                &missing_ranges);
            if (rc != 0) {
                errx(
                    EX_SOFTWARE,
                    "bcap library error -- %s",
                    monad_bcap_get_last_error());
            }
            if (!TAILQ_EMPTY(&missing_ranges.head)) {
                // We're missing blocks; delegate to the fetch program to
                // retrieve them
                fetch_missing_block_ranges(
                    resolved_fetch_command,
                    cfg->block_dir_path,
                    &missing_ranges,
                    cfg->verbose > 0);
            }
            monad_bcap_block_range_list_free(&missing_ranges);
        }
        for (uint64_t b = unseen.block_start + 1; b <= unseen.block_end; ++b) {
            struct monad_evcap_event_section event_section;
            struct monad_evcap_event_iter evcap_iter;
            struct monad_evcap_reader *evcap_reader;
            struct monad_evcap_section_desc const *block_sd;
            struct monad_event_descriptor const *evcap_event;

            // Try to open block b; we expect it to always be there, because
            // the call to `fetch_missing_block_ranges` should have ended up
            // calling err(3) otherwise; this gives back a reader for an
            // "event capture" (evcap) file
            if (monad_bcap_archive_open_block_reader(
                    block_archive,
                    b,
                    nullptr,
                    0,
                    nullptr,
                    &evcap_reader,
                    &block_sd) != 0) {
                errx(
                    EX_SOFTWARE,
                    "bcap library error -- %s",
                    monad_bcap_get_last_error());
            }

            // Event capture files contain multiple sections, and this API call
            // will "open" the section of the file containing the events, as
            // described by the section description `block_sd` given to us by
            // the archive layer.
            //
            // This is a potentially expensive step, because the section
            // contents can be zstd-compressed. It is important to remember to
            // close this section object because it will hold dynamically
            // allocated memory whenever the section needed to be decompressed
            if (monad_evcap_event_section_open(
                    &event_section, evcap_reader, block_sd) != 0) {
                errx(
                    EX_SOFTWARE,
                    "evcap_reader library error -- %s",
                    monad_evcap_reader_get_last_error());
            }

            // Open an iterator to all the events in the section, and use it
            // to read and print all the events in it
            monad_evcap_event_section_open_iterator(
                &event_section, &evcap_iter);
            while (g_should_stop == 0 &&
                   monad_evcap_event_iter_next(
                       &evcap_iter, &evcap_event, &payload) !=
                       MONAD_EVCAP_READ_END) {
                print_event(
                    monad_evsrc_any_from(&event_section),
                    evcap_event,
                    payload,
                    out);
            }
            monad_evcap_event_section_close(&event_section);
            monad_evcap_reader_destroy(evcap_reader);
            last_finalized_block = b;
            if (g_should_stop != 0) {
                return;
            }
        }

        // Because recovery takes time, more blocks may have finalized while
        // we were processing replay events. Our strategy is incremental: keep
        // using replay to close the gap until the gap is less than a certain
        // size, then we're "caught up enough" to switch to the live event ring.
        unseen =
            compute_unseen_block_range(unseen.block_end, event_ring, pidfd);
    }
    while (g_should_stop == 0 &&
           unseen.block_end - unseen.block_start > LIVE_RING_BLOCK_THRESHOLD);

    // Initialize an event ring iterator the points into the live ring, and
    // rewind it to the point where it will replay events after the initial
    // proposal of the last finalized block
    if (monad_event_ring_init_iterator(event_ring, &ring_iter) != 0) {
        errx(
            EX_SOFTWARE,
            "event ring library error -- %s",
            monad_event_ring_get_last_error());
    }
    if (!monad_exec_iter_rewind_for_simple_replay(
            &ring_iter, unseen.block_start, &live_event, &payload)) {
        // We were within the threshold, but somehow the rewind failed
        // TODO(ken): it is extremely unlikely this can ever happen, and we
        //  should think more about what the right to do is in this case
        //  (what could have happened, for it to be possible that we see
        //  this?)
        fprintf(
            stderr,
            "warning: gap (%lu, %lu] is small but could not rewind "
            "to immediate following %lu",
            unseen.block_start,
            unseen.block_end,
            unseen.block_start);
        last_finalized_block = unseen.block_start;
        goto RecoverAgain;
    }
    if (cfg->verbose > 0) {
        fprintf(
            stderr,
            "%s: switching to live event ring after last finalized block %lu",
            __progname,
            unseen.block_start);
    }

    while (g_should_stop == 0) {
        uint64_t new_finalized_block;

        switch (monad_event_ring_iter_try_next(&ring_iter, &live_event)) {
        case MONAD_EVENT_RING_NOT_READY:
            if ((not_ready_count++ & ((1UL << 25) - 1)) == 0) {
                // See comment in eventwatch.c
                fflush(out);
                if (process_has_exited(pidfd)) {
                    g_should_stop = 1;
                }
            }
            continue; // Nothing produced yet

        case MONAD_EVENT_RING_GAP:
            fprintf(
                stderr,
                "ERROR: event gap from %lu -> %lu, re-entering recovery\n",
                ring_iter.cur_seqno,
                monad_event_ring_get_last_written_seqno(event_ring, false));
            goto RecoverAgain;

        case MONAD_EVENT_RING_SUCCESS:
            payload = monad_event_ring_payload_peek(event_ring, &live_event);
            print_event(
                monad_evsrc_any_from(event_ring), &live_event, payload, out);
            // Keep track of the last finalized block number, so we can recover
            // again when a gap occurs
            if (live_event.event_type == MONAD_EXEC_BLOCK_FINALIZED) {
                if (monad_exec_get_block_number(
                        event_ring,
                        &live_event,
                        payload,
                        &new_finalized_block) == false) {
                    errx(
                        EX_SOFTWARE,
                        "finalization of %lu expired immediately?",
                        live_event.seqno);
                }
                if (new_finalized_block != last_finalized_block + 1) {
                    // This is a very rare corner case that can happen if the
                    // blockchain daemons are restarted in an unusual way
                    // different from what the user guide recommends; it is
                    // described in detail as "Case 3" in the
                    // "Detecting gaps and restoring service" section of the
                    // SDK documentation on historicl recovery
                    if (cfg->verbose) {
                        fprintf(
                            stderr,
                            "%s: unexpected finalization jump: %lu -> %lu",
                            __progname,
                            last_finalized_block,
                            new_finalized_block);
                    }
                    goto RecoverAgain;
                }
                last_finalized_block = new_finalized_block;
            }
            break;
        }
        not_ready_count = 0;
    }
}

static void reconnect_loop(
    struct config const *cfg, struct monad_bcap_archive *block_archive,
    char const *resolved_fetch_command, FILE *out)
{
    char event_ring_pathbuf[PATH_MAX];
    struct monad_event_ring exec_ring;
    int writer_pidfd;

    if (monad_event_resolve_ring_file(
            MONAD_EVENT_DEFAULT_HUGETLBFS,
            cfg->event_ring_path,
            event_ring_pathbuf,
            sizeof event_ring_pathbuf) != 0) {
        errx(
            EX_SOFTWARE,
            "event library error -- %s",
            monad_event_ring_get_last_error());
    }

    memset(&exec_ring, 0, sizeof exec_ring);
    while (g_should_stop == 0) {
        // Open the event ring. This will tell us what block we're currently
        // on, and eventually we'll switch over to live reading once we've
        // recovered
        if (open_event_ring(event_ring_pathbuf, &exec_ring, &writer_pidfd) !=
            0) {
            // Whenever open_event_ring returns non-zero, it's either a rare
            // IPC race (and we should try again) or EINTR, and we should check
            // g_should_stop again
            continue;
        }
        event_loop(
            cfg,
            &exec_ring,
            block_archive,
            resolved_fetch_command,
            writer_pidfd,
            out);
        (void)close(writer_pidfd);
    }
    monad_event_ring_unmap(&exec_ring);
}

int main(int argc, char **argv)
{
    struct monad_bcap_archive *block_archive;

    struct config const cfg = parse_arguments(argc, argv);
    signal(SIGINT, handle_signal);

    // Resolve the external command which will fetch missing blocks, if our
    // local block directory does not have them
    char *const fetch_command =
        resolve_fetch_command(cfg.fetch_command, cfg.verbose);
    if (fetch_command == nullptr) {
        errx(
            EX_UNAVAILABLE,
            "no fetch command `%s` found on $PATH, $PWD, or "
            "the executable's directory",
            cfg.fetch_command);
    }

    // Open the "finalized block archive" (FBA) directory
    int const block_dirfd =
        open(cfg.block_dir_path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (block_dirfd == -1) {
        err(EX_USAGE,
            "open of finalized block directory `%s` failed",
            cfg.block_dir_path);
    }
    if (monad_bcap_archive_open(
            &block_archive, block_dirfd, cfg.block_dir_path) != 0) {
        errx(
            EX_SOFTWARE,
            "blockcap library error -- %s",
            monad_bcap_get_last_error());
    }
    // monad_bcap_archive_open will dup(2) the fd, we don't need it anymore
    (void)close(block_dirfd);

    // The outer loop of the program waits for execution daemon to (re)start,
    // and each time it re-appears, we begin working again
    reconnect_loop(&cfg, block_archive, fetch_command, stdout);

    // Cleanup
    free(fetch_command);
    monad_bcap_archive_close(block_archive);

    return 0;
}
