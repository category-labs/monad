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
#include <poll.h>
#include <signal.h>
#include <sys/mman.h>
#include <syscall.h>
#include <sysexits.h>
#include <time.h>
#include <unistd.h>

#include <category/core/event/event_iterator.h>
#include <category/core/event/event_metadata.h>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_iter_help.h>

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
    MONAD_EVENT_DEFAULT_EXEC_RING_PATH);
    exit(0);
}

struct option const longopts[] = {
    {"help", no_argument, nullptr, 'h'},
    {}
};

int parse_options(int argc, char **argv)
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

void handle_signal(int)
{
    g_should_stop = 1;
}

static bool process_has_exited(int pidfd)
{
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
        fprintf(stderr, "ERROR: event %lu payload lost!\n", event->seqno);
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
    time_parts = ldiv(event->record_epoch_nanos, 1'000'000'000L);
    if (time_parts.quot != last_second) {
        // A new second has ticked. Reformat the per-second time buffer.
        struct tm;
        last_second = time_parts.quot;
        strftime(
            time_buf, sizeof time_buf, "%H:%M:%S", localtime(&last_second));
    }

    // Print a summary line of this event
    // <HH:MM::SS.nanos> <event-c-name> [<event-type> <event-type-hex>]
    //     SEQ: <sequence-no> LEN: <payload-length>
    o += sprintf(
        event_buf,
        "%s.%09ld: %s [%hu 0x%hx] SEQ: %lu LEN: %u BUF_OFF: %lu",
        time_buf,
        time_parts.rem,
        event_md->c_name,
        event->event_type,
        event->event_type,
        event->seqno,
        event->payload_size,
        event->payload_buf_offset);
    if (event->user[MONAD_FLOW_BLOCK_SEQNO] != 0) {
        // When `event->user[MONAD_FLOW_BLOCK_SEQNO]` is non-zero, it is set to
        // the sequence number of the MONAD_EXEC_BLOCK_START event that started
        // the block that this event is part of. This code tries to read the
        // payload of that event, to print the block number.
        struct monad_event_descriptor start_block_event;
        struct monad_exec_block_start const *block_start = nullptr;
        if (monad_event_ring_try_copy(
                event_ring,
                event->user[MONAD_FLOW_BLOCK_SEQNO],
                &start_block_event)) {
            block_start =
                monad_event_ring_payload_peek(event_ring, &start_block_event);
        }
        if (block_start) {
            uint64_t const block_number = block_start->exec_input.number;
            if (monad_event_ring_payload_check(
                    event_ring, &start_block_event)) {
                o += sprintf(o, " BLK: %lu", block_number);
            }
            else {
                o += sprintf(o, " BLK: <LOST>");
            }
        }
    }
    if (event->user[MONAD_FLOW_TXN_ID] != 0) {
        o += sprintf(o, " TXN: %lu", event->user[MONAD_FLOW_TXN_ID] - 1);
    }
    *o++ = '\n';
    fwrite(event_buf, (size_t)(o - event_buf), 1, out);

    // Dump the event payload as a hexdump to simplify the example. If you
    // want the real event payloads, they can be type cast into the appropriate
    // payload data type from `event_types.h`, e.g.:
    //
    //    switch (event->type) {
    //    case MONAD_EVENT_TXN_START:
    //        act_on_start_transaction(
    //            (struct monad_event_txn_header const *)payload, ...);
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
                fflush(out);
                if (process_has_exited(pidfd)) {
                    g_should_stop = 1;
                }
            }
            continue; // Nothing produced yet

        case MONAD_EVENT_GAP:
            fprintf(
                stderr,
                "ERROR: event gap from %lu -> %lu, resetting\n",
                iter->read_last_seqno,
                __atomic_load_n(&iter->control->last_seqno, __ATOMIC_ACQUIRE));
            monad_event_iterator_reset(iter);
            not_ready_count = 0;
            continue;

        case MONAD_EVENT_SUCCESS:
            not_ready_count = 0;
            break; // Handled in the main loop body
        }
        print_event(event_ring, &event, out);
    }
}

static void find_initial_iteration_point(
    struct monad_event_ring const *event_ring,
    struct monad_event_iterator *iter)
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
    char const *event_ring_path = MONAD_EVENT_DEFAULT_EXEC_RING_PATH;
    int const pos_arg_idx = parse_options(argc, argv);

    if (argc - pos_arg_idx > 1) {
        usage(stderr);
        return EX_USAGE;
    }
    if (pos_arg_idx + 1 == argc) {
        event_ring_path = argv[pos_arg_idx];
    }
    signal(SIGINT, handle_signal);

    // The first step is to oepn and event ring file and mmap its shared memory
    // segments into our process' address space. If this is successful, we'll
    // be able to create one or more iterators over that ring's events.
    struct monad_event_ring exec_ring;
    int const ring_fd = open(event_ring_path, O_RDONLY);
    if (ring_fd == -1) {
        err(EX_CONFIG, "open of event ring path `%s` failed", event_ring_path);
    }
    if (monad_event_ring_mmap(
            &exec_ring, PROT_READ, MAP_HUGETLB, ring_fd, 0, event_ring_path) !=
        0) {
        goto Error;
    }

    // Our mmap was successful; this program assumes that we'll be looking
    // at the event ring that holds core execution events. The execution
    // process can expose other kinds of event rings for other purposes (e..g,
    // performance tracing). Make sure we're looking at the right kind of
    // ring.
    if (monad_event_ring_check_content_type(
            &exec_ring,
            MONAD_EVENT_CONTENT_TYPE_EXEC,
            g_monad_exec_event_schema_hash) != 0) {
        goto Error;
    }

    // A helper function allows us to find the pids of all processes which have
    // opened the event ring for writing. For the execution event ring, we
    // expect there will only be one writer (the execution daemon). We'll use
    // this to open a pidfd_open(2) descriptor referring to the execution
    // process to detect when it dies.
    pid_t writer_pid;
    size_t n_pids = 1;
    if (monad_event_ring_find_writer_pids(ring_fd, &writer_pid, &n_pids) != 0) {
        goto Error;
    }
    if (n_pids == 0) {
        errno = EOWNERDEAD;
        err(EX_SOFTWARE,
            "writer of event ring `%s` has exited",
            event_ring_path);
    }
    int pidfd = (int)syscall(SYS_pidfd_open, writer_pid, 0);
    if (pidfd == -1) {
    }
    // We no longer need the event ring file descriptor
    (void)close(ring_fd);

    // Create an iterator to read from the event ring
    struct monad_event_iterator iter;
    if (monad_event_ring_init_iterator(&exec_ring, &iter) != 0) {
        goto Error;
    }

    // Move the iterator to the start of the most recently produced block
    find_initial_iteration_point(&exec_ring, &iter);

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
