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
 * Execution event observer utility - this small CLI application serves as a
 * demo of how to use the event client and iterator APIs from an external
 * process.
 */

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <err.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <sys/mman.h>
#include <sysexits.h>
#include <time.h>
#include <unistd.h>

#if defined(__linux__)
    #include <syscall.h>
constexpr bool PLATFORM_LINUX = true;
#else
constexpr bool PLATFORM_LINUX = false;
    #define SYS_pidfd_open -1
    #if defined(__clang__)
        #pragma clang diagnostic ignored "-Wdeprecated-declarations"
    #endif
#endif

#include <category/core/event/event_iterator.h>
#include <category/core/event/event_metadata.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_iter_help.h>

constexpr int PIDFD_SNAPSHOT = -2;

static void usage(FILE *out)
{
    extern char const *__progname;
    fprintf(out, "usage: %s [-h] [<exec-event-ring>]\n", __progname);
}

// clang-format off

[[noreturn]] static void help()
{
    usage(stdout);
    fprintf(stdout,
"\n"
"execution event observer example program\n"
"\n"
"Options:\n"
"  -h | --help   print this message\n"
"\n"
"Positional arguments:\n"
"  <exec-event-ring>   path of execution event ring shared memory file\n"
"                        [default: %s]\n",
    MONAD_EVENT_DEFAULT_EXEC_FILE_NAME);
    exit(0);
}

struct option const longopts[] = {
    {"help", no_argument, nullptr, 'h'},
    {}
};

static int parse_options(int argc, char **argv)
{
    int ch;

    while ((ch = getopt_long(argc, argv, "h", longopts, nullptr)) != -1) {
        switch (ch) {
        case 'h':
            help();

        default:
            usage(stderr);
            exit(EX_USAGE);
        }
    }

    return optind;
}

// clang-format on

static sig_atomic_t g_should_stop;

static void handle_signal(int)
{
    g_should_stop = 1;
}

static bool process_has_exited(int pidfd)
{
    if (pidfd == -1) {
        // pidfd being -1 means "disable the detection feature"
        return false;
    }
    if (pidfd == PIDFD_SNAPSHOT) {
        return true;
    }
    struct pollfd pfd = {.fd = pidfd, .events = POLLIN};
    return poll(&pfd, 1, 0) == -1 || (pfd.revents & POLLIN) == POLLIN;
}

static void hexdump_event_payload(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, FILE *out)
{
    static char hexdump_buf[1 << 25];
    char *o = hexdump_buf;
    uint8_t const *const payload =
        monad_event_ring_payload_peek(event_ring, event);
    uint8_t const *const payload_end = payload + event->payload_size;
    for (uint8_t const *line = payload; line < payload_end; line += 16) {
        // Print one line of the dump, which is 16 bytes, in the form:
        // <offset> <8 bytes> <8 bytes>
        o += sprintf(o, "%08lx ", line - payload);
        for (uint8_t b = 0; b < 16 && line + b < payload_end; ++b) {
            o += sprintf(o, "%02x", line[b]);
            if (b == 7) {
                *o++ = ' '; // Extra padding after 8 bytes
            }
        }
        *o++ = '\n';

        // Every 512 bytes, check if the payload is still valid; the + 16 byte
        // bias is to prevent checking the first iteration
        if ((line - payload + 16) % 512 == 0 &&
            !monad_event_ring_payload_check(event_ring, event)) {
            break; // Escape to the end, which checks the final time
        }
    }

    if (!monad_event_ring_payload_check(event_ring, event)) {
        fprintf(
            stderr,
            "ERROR: event %lu payload expired!\n",
            (unsigned long)event->seqno);
    }
    else {
        fwrite(hexdump_buf, (size_t)(o - hexdump_buf), 1, out);
    }
}

static void print_event(
    struct monad_event_ring const *event_ring,
    struct monad_event_descriptor const *event, FILE *out)
{
    static char time_buf[32];
    static time_t last_second = 0;

    ldiv_t time_parts;
    char event_buf[256];
    char *o = event_buf;

    struct monad_event_metadata const *event_md =
        &g_monad_exec_event_metadata[event->event_type];

    // An optimization to only do the string formatting of the %H:%M:%S part
    // of the time each second when it changes, because strftime(3) is slow
    time_parts = ldiv((long)event->record_epoch_nanos, 1'000'000'000L);
    if (time_parts.quot != last_second) {
        // A new second has ticked. Reformat the per-second time buffer.
        struct tm;
        last_second = time_parts.quot;
        strftime(
            time_buf, sizeof time_buf, "%H:%M:%S", localtime(&last_second));
    }

    // Print a summary line of this event
    // <HH:MM::SS.nanos> <event-c-name> [<event-type> <event-type-hex>]
    //     SEQ: <sequence-number> LEN: <payload-size>
    //     BUF_OFF: <payload-buffer-offset>
    o += sprintf(
        event_buf,
        "%s.%09ld: %s [%hu 0x%hx] SEQ: %lu LEN: %u BUF_OFF: %lu",
        time_buf,
        time_parts.rem,
        event_md->c_name,
        event->event_type,
        event->event_type,
        (unsigned long)event->seqno,
        event->payload_size,
        (unsigned long)event->payload_buf_offset);
    if (event->content_ext[MONAD_FLOW_BLOCK_SEQNO] != 0) {
        // When `event->content_ext[MONAD_FLOW_BLOCK_SEQNO]` is non-zero, it
        // is set to the sequence number of the MONAD_EXEC_BLOCK_START event
        // that started the block that this event is part of. This code tries
        // to read the payload of that event, to print the block number.
        struct monad_event_descriptor start_block_event;
        struct monad_exec_block_start const *block_start = nullptr;
        if (monad_event_ring_try_copy(
                event_ring,
                event->content_ext[MONAD_FLOW_BLOCK_SEQNO],
                &start_block_event)) {
            block_start =
                monad_event_ring_payload_peek(event_ring, &start_block_event);
        }
        if (block_start) {
            uint64_t const block_number = block_start->eth_block_input.number;
            if (monad_event_ring_payload_check(
                    event_ring, &start_block_event)) {
                o += sprintf(o, " BLK: %lu", (unsigned long)block_number);
            }
            else {
                o += sprintf(o, " BLK: <LOST>");
            }
        }
    }
    if (event->content_ext[MONAD_FLOW_TXN_ID] != 0) {
        o += sprintf(
            o,
            " TXN: %lu",
            (unsigned long)(event->content_ext[MONAD_FLOW_TXN_ID] - 1));
    }
    *o++ = '\n';
    fwrite(event_buf, (size_t)(o - event_buf), 1, out);

    // Dump the event payload as a hexdump to simplify the example. If you
    // wanted specific data about event payloads, they can be type cast into
    // the appropriate payload data type from `exec_event_ctypes.h`, e.g.:
    //
    //    switch (event->event_type) {
    //    case MONAD_EXEC_TXN_HEADER_START:
    //        act_on_start_transaction(
    //            (struct monad_exec_txn_header_start const *)payload, ...);
    //        break;
    //
    //    // ... switch cases for other event types
    //    };
    hexdump_event_payload(event_ring, event, out);
}

// The main event processing loop of the application
static void event_loop(
    struct monad_event_ring const *event_ring,
    struct monad_event_iterator *iter, int pidfd, FILE *out)
{
    struct monad_event_descriptor event;
    uint64_t not_ready_count = 0;

    while (g_should_stop == 0) {
        switch (monad_event_iterator_try_next(iter, &event)) {
        case MONAD_EVENT_NOT_READY:
            if ((not_ready_count++ & ((1U << 25) - 1)) == 0) {
                // The above guard prevents us from calling process_has_exited
                // too often, as it is orders of magnitude slower than the cost
                // of an event ring poll
                fflush(out);
                if (process_has_exited(pidfd)) {
                    g_should_stop = 1;
                }
            }
            continue; // Nothing produced yet

        case MONAD_EVENT_GAP:
            fprintf(
                stderr,
                "ERROR: event gap from %lu -> %lu, resetting iterator\n",
                (unsigned long)iter->read_last_seqno,
                (unsigned long)__atomic_load_n(
                    &iter->control->last_seqno, __ATOMIC_ACQUIRE));
            monad_event_iterator_reset(iter);
            break;

        case MONAD_EVENT_SUCCESS:
            print_event(event_ring, &event, out);
            break;
        }
        not_ready_count = 0;
    }
}

static void find_initial_iteration_point(struct monad_event_iterator *iter)
{
    // This function is not strictly necessary, but it is probably useful for
    // most use cases. When an iterator is initialized via a call to
    // `monad_event_ring_init_iterator`, the initial iteration point is set to
    // the most recently produced event (if there is one).
    //
    // The rationale for starting with the most recent event is that the first
    // event is usually already gone, i.e., overwritten by a later event in
    // the ring buffer. That will usually be the case unless your application
    // starts very close to the same time as the execution daemon. Thus,
    // there's no "natural" place to start, so we might as well start with
    // the most recent event since that gives us the maximum "cushion" of
    // buffer space before experiencing a gap.
    //
    // Usually this means you will be starting in the middle of a block. This
    // is not ideal, since processing tends to be block oriented: for most
    // use cases, you need to see BLOCK_START before you can do anything with
    // any subsequent events (this is so that you can track the proposal
    // through its consensus states).
    //
    // This function checks if the iterator is pointing "in the middle of"
    // a block (i.e., not at BLOCK_START) and if it is, rewinds it to the
    // previous BLOCK_START event. In the (very unlikely) case that the
    // iterator is already pointing at BLOCK_START, this will rewind it to the
    // previous consensus event, i.e., a nearby BLOCK_QC, BLOCK_FINALIZED, or
    // BLOCK_VERIFIED.
    //
    // The event ring typically holds hundreds of blocks, so moving backward
    // doesn't materially increase the risk that we'll fall behind and gap.
    (void)monad_exec_iter_consensus_prev(iter, MONAD_EXEC_BLOCK_START, nullptr);
}

int main(int argc, char **argv)
{
    char event_ring_pathbuf[PATH_MAX];
    char const *event_ring_input = MONAD_EVENT_DEFAULT_EXEC_FILE_NAME;
    int const pos_arg_idx = parse_options(argc, argv);

    if (argc - pos_arg_idx > 1) {
        usage(stderr);
        return EX_USAGE;
    }
    if (pos_arg_idx + 1 == argc) {
        event_ring_input = argv[pos_arg_idx];
    }

    // Event ring shared memory files can be located anywhere, but there is a
    // performance benefit to placing them on certain filesystems; consequently,
    // there are several functions related to opening / creating event ring
    // files at an optimal default location; a common pattern is to accept any
    // filename, but with a default filename if nothing is specified (in this
    // case, MONAD_EVENT_DEFAULT_EXEC_FILE_NAME); the below function will place
    // "pure" file names (i.e., with no '/' in path) in the best subdirectory
    if (monad_event_resolve_ring_file(
            MONAD_EVENT_DEFAULT_HUGETLBFS,
            event_ring_input,
            event_ring_pathbuf,
            sizeof event_ring_pathbuf) != 0) {
        goto Error;
    }

    signal(SIGINT, handle_signal);

    // The first step is to open an event ring file, so that we can mmap its
    // shared memory segments into our process' address space.
    int ring_fd = open(event_ring_pathbuf, O_RDONLY);
    if (ring_fd == -1) {
        err(EX_CONFIG,
            "open of event ring path `%s` failed",
            event_ring_pathbuf);
    }

    // We could pass the `ring_fd` file descriptor to monad_event_ring_mmap now,
    // but we first call the helper function monad_event_is_snapshot_file. This
    // function checks if `ring_fd` appears to be an event ring "snapshot."
    //
    // A "snapshot file" is just the zstd-compressed contents of an event ring
    // shared memory file, exactly as it appeared at the moment when a snapshot
    // of it was taken. It is no longer being written to, therefore it can be
    // highly compressed (which is the sole distinction between a "normal" event
    // ring file and a snapshot).
    //
    // Snapshots allows the user to replay a fixed set of known events, and are
    // useful during software testing and development; this example supports
    // both live event rings and snapshots to make sure users know about them.
    bool is_snapshot;
    if (monad_event_is_snapshot_file(
            ring_fd, event_ring_pathbuf, &is_snapshot) != 0) {
        goto Error; // Cannot determine if snapshot is fatal
    }
    if (is_snapshot) {
        // We have a snapshot; use monad_event_decompress_snapshot_fd to
        // decompress it, so that it can be mapped into our address space like
        // a normal event ring file. We then close the original `ring_fd` and
        // replace it with the decompressed temporary file.
        //
        // After this, the API (and the library implementation itself) make no
        // distinction between a "normal" event ring and a decompressed snapshot
        // (and are not even aware of the difference). Thus, a decompressed
        // snapshot is indistinguishable from a "live" event ring file whose
        // writer process (the execution daemon) has died and left behind an
        // orphaned file on the system. The latter should not happen often, but
        // if the execution daemon dies ungracefully (e.g., by SIGKILL) the
        // event ring file won't be cleaned up and will be a "zombie".
        //
        // Thus we need to reference the `is_snapshot` boolean again later,
        // because we sometimes treat snapshots a bit differently. The biggest
        // difference is how we treat an event ring that has not produced events
        // for a while. In the snapshot case, that means we're done and should
        // exit the program or test. For a live event ring, we need to run some
        // kind of logic to decide if it's worth waiting around for new events
        // to be produced, or whether we should assume the execution daemon has
        // crashed or hung.
        int snapshot_fd;
        if (monad_event_decompress_snapshot_fd(
                ring_fd, 0, event_ring_pathbuf, &snapshot_fd) != 0) {
            goto Error;
        }
        (void)close(ring_fd);
        ring_fd = snapshot_fd;
    }

    // Map the shared memory segments of the event ring into our address space.
    // If this is successful, we'll be able to create one or more iterators
    // over that ring's events.
    struct monad_event_ring exec_ring;
    if (monad_event_ring_mmap(
            &exec_ring, PROT_READ, 0, ring_fd, 0, event_ring_pathbuf) != 0) {
        goto Error;
    }

    // Our mmap was successful; this program assumes that we'll be looking
    // at the event ring that holds core execution events. The execution
    // process can expose other kinds of event rings for other purposes (e.g.,
    // performance tracing). Make sure we're looking at the right kind of
    // event content.
    if (monad_event_ring_check_content_type(
            &exec_ring,
            MONAD_EVENT_CONTENT_TYPE_EXEC,
            g_monad_exec_event_schema_hash) != 0) {
        goto Error;
    }

    // A helper function allows us to find the pid of a process which has opened
    // an event ring for exclusive access. For the execution event ring, we
    // expect there will only be one writer (the execution daemon). Once we've
    // discovered the pid of the execution daemon, we'll open a pidfd_open(2)
    // descriptor referring to its process, to easily detect when it dies.
    // If this is a snapshot we won't do any of this, since there is no writer.
    int pidfd = -1;
    if (is_snapshot) {
        pidfd = PIDFD_SNAPSHOT;
    }
    else if (PLATFORM_LINUX) {
        pid_t writer_pid;
        if (monad_event_ring_query_excl_writer_pid(ring_fd, &writer_pid) != 0) {
            goto Error;
        }
        pidfd = (int)syscall(SYS_pidfd_open, writer_pid, 0);
        if (pidfd == -1) {
            err(EX_OSERR, "pidfd_open of writer pid %d failed", writer_pid);
        }
    }

    // After we have mmap'ed the event ring file's shared memory segments into
    // our address space and (optionally) created the pidfd, we no longer need
    // to keep the file descriptor open
    (void)close(ring_fd);

    // Create an iterator to read from the event ring
    struct monad_event_iterator iter;
    if (monad_event_ring_init_iterator(&exec_ring, &iter) != 0) {
        goto Error;
    }

    // If this is a snapshot, move the iterator to the start of the event ring;
    // if this is a live event ring, move the iterator to the start of the most
    // recently produced block
    if (is_snapshot) {
        monad_event_iterator_set_seqno(&iter, 1);
    }
    else {
        find_initial_iteration_point(&iter);
    }

    // Read events from the ring until SIGINT or the monad process exits
    event_loop(&exec_ring, &iter, pidfd, stdout);

    // Clean up: unmap the execution event ring from our address space
    monad_event_ring_unmap(&exec_ring);
    return 0;

Error:
    // Our error message doesn't need to state what failed (i.e., we don't
    // need to mention `monad_event_ring_open` in the error message)
    // because the library's error system includes this
    errx(
        EX_SOFTWARE,
        "event library error -- %s",
        monad_event_ring_get_last_error());
}
