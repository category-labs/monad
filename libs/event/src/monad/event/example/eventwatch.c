/**
 * @file
 *
 * Execution event observer utility - this small CLI application serves as a
 * demo of how to use the event client and iterator APIs from an external
 * process.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <err.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <sysexits.h>

#include <monad/event/event.h>
#include <monad/event/event_client.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>

// By default, failure to respond within 1 second means we assume the
// server is dead
struct monad_event_connect_options const DEFAULT_CONNECT_OPTIONS = {
    .socket_path = MONAD_EVENT_DEFAULT_SOCKET_PATH,
    .socket_timeout = {.tv_sec = 1, .tv_usec = 0}};

static void usage(FILE *out)
{
    extern char const *__progname;
    fprintf(out, "usage: %s [-h] [-t <timeout>] [<socket-file>]\n", __progname);
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
"  -h | --help                print this message\n"
"  -t | --timeout <seconds>   server socket timeout, in seconds; zero\n"
"                                 disables [default: %ld]\n"
"\n"
"Positional arguments:\n"
"  <socket-file>  path to the execution daemons' UNIX domain socket\n"
"                 [default: %s]\n",
    DEFAULT_CONNECT_OPTIONS.socket_timeout.tv_sec,
    DEFAULT_CONNECT_OPTIONS.socket_path);
    exit(0);
}

struct option const longopts[] = {
    {"help", no_argument, nullptr, 'h'},
    {"timeout", required_argument, nullptr, 't'},
    {}
};

int parse_options(int argc, char **argv, struct monad_event_connect_options *options)
{
    int ch;
    char *parse_end;
    unsigned long timeout;

    while ((ch = getopt_long(argc, argv, "ht:", longopts, nullptr)) != -1) {
        switch (ch) {
        case 'h':
            help();

        case 't':
            timeout = strtoul(optarg, &parse_end, 10);
            if (parse_end != optarg + strlen(optarg)) {
                errno = EINVAL;
                err(EX_USAGE, "could not parse %s as a socket timeout value",
                    optarg);
            }
            options->socket_timeout.tv_sec = (time_t)timeout;
            break;

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

static bool is_txn_event(enum monad_event_type type)
{
    switch (type) {
    case MONAD_EVENT_TXN_START:
        [[fallthrough]];
    case MONAD_EVENT_TXN_EXEC_ERROR:
        [[fallthrough]];
    case MONAD_EVENT_TXN_REJECT:
        [[fallthrough]];
    case MONAD_EVENT_TXN_LOG:
        [[fallthrough]];
    case MONAD_EVENT_TXN_RECEIPT:
        [[fallthrough]];
    case MONAD_EVENT_WR_ACCT_STATE_BALANCE:
        [[fallthrough]];
    case MONAD_EVENT_WR_ACCT_STATE_STORAGE:
        return true;

    default:
        return false;
    }
}

static void hexdump_event_payload(
    struct monad_event_iterator const *iter,
    struct monad_event_descriptor const *event, FILE *out)
{
    static char hexdump_buf[1 << 25];
    char *o = hexdump_buf;
    uint8_t const *const payload = monad_event_payload_peek(iter, event);
    uint8_t const *const payload_end = payload + event->length;
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
            !monad_event_payload_check(iter, event)) {
            break; // Escape to the end, which checks the final time
        }
    }

    if (!monad_event_payload_check(iter, event)) {
        fprintf(stderr, "ERROR: event %lu payload lost!\n", event->seqno);
    }
    else {
        fwrite(hexdump_buf, (size_t)(o - hexdump_buf), 1, out);
    }
}

static void print_event(
    struct monad_event_iterator *iter,
    struct monad_event_descriptor const *event,
    struct monad_event_thread_info const *thr_info,
    struct monad_event_block_exec_header const *block_exec_header, FILE *out)
{
    static char timebuf[32];
    static time_t last_second = 0;

    ldiv_t time_parts;
    char event_buf[256];
    char *o = event_buf;

    struct monad_event_metadata const *event_md =
        &g_monad_event_metadata[event->type];

    time_parts = ldiv(event->epoch_nanos, 1'000'000'000L);
    if (time_parts.quot != last_second) {
        // A new second has ticked. Reformat the per-second time buffer.
        struct tm;
        last_second = time_parts.quot;
        strftime(timebuf, sizeof timebuf, "%H:%M:%S", localtime(&last_second));
    }

    // Print a summary line of this event
    // <HH:MM::SS.nanos> <event-c-name> [<event-type> <event-type-hex>]
    //     SEQ: <sequence-no> LEN: <payload-length>
    //     SRC: <source-id> [<thread-name> <thread-id>]
    o += sprintf(
        event_buf,
        "%s.%09ld: %s [%hu 0x%hx] SEQ: %lu LEN: %u SRC: %u [%s (%lu)]",
        timebuf,
        time_parts.rem,
        event_md->c_name,
        event->type,
        event->type,
        event->seqno,
        event->length,
        event->source_id,
        thr_info->thread_name,
        thr_info->thread_id);
    if (event->block_flow_id) {
        o += sprintf(
            o,
            " BLK: %lu [R: %lu]",
            block_exec_header->number,
            block_exec_header->round);
    }
    if (is_txn_event(event->type)) {
        o += sprintf(o, " TXN: %u", event->txn_num);
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
    hexdump_event_payload(iter, event, out);
}

// The main event processing loop of the application
static void
event_loop(struct monad_event_imported_ring const *import, FILE *out)
{
    struct monad_event_descriptor event;
    struct monad_event_iterator iter;
    struct monad_event_thread_info const *const thread_table =
        import->proc->thread_table;
    struct monad_event_block_exec_header const *const block_header_table =
        import->proc->block_header_table;
    uint64_t not_ready_count = 0;

    monad_event_imported_ring_init_iter(import, &iter);
    while (g_should_stop == 0) {
        switch (monad_event_iterator_try_next(&iter, &event)) {
        case MONAD_EVENT_NOT_READY:
            if ((not_ready_count++ & ((1U << 20) - 1)) == 0) {
                fflush(out);
                if (!monad_event_proc_is_connected(import->proc)) {
                    g_should_stop = 1;
                }
            }
            continue; // Nothing produced yet

        case MONAD_EVENT_GAP:
            fprintf(
                stderr,
                "ERROR: event gap from %lu -> %lu, resetting\n",
                iter.read_last_seqno,
                event.seqno);
            monad_event_iterator_reset(&iter);
            continue;

        case MONAD_EVENT_SUCCESS:
            break; // Handled in the main loop body

        case MONAD_EVENT_PAYLOAD_EXPIRED:
            unreachable(); // Never returned by monad_event_iterator_try_next
        }
        not_ready_count = 0;
        print_event(
            &iter,
            &event,
            &thread_table[event.source_id],
            &block_header_table[event.block_flow_id],
            out);
    }
}

int main(int argc, char **argv)
{
    struct monad_event_connect_options options = DEFAULT_CONNECT_OPTIONS;

    int const pos_arg_idx = parse_options(argc, argv, &options);
    if (argc - pos_arg_idx > 1) {
        usage(stderr);
        return EX_USAGE;
    }
    if (pos_arg_idx + 1 == argc) {
        options.socket_path = argv[pos_arg_idx];
    }
    signal(SIGINT, handle_signal);

    // We start by connecting to a running instance of the monad execution
    // process
    struct monad_event_proc *exec_proc;
    if (monad_event_proc_connect(&options, &exec_proc) != 0) {
        errx(
            EX_SOFTWARE,
            "monad_event_proc_connect failed: %s",
            monad_event_proc_get_last_error());
    }

    // Just connecting to the process does not do much: the critical thing
    // is to "import" an event ring. Import here means that we'll map all the
    // ring's shared memory segments into our process' address space. If this
    // is successful, we'll be able to create one or more iterators over that
    // ring's events.
    struct monad_event_imported_ring *exec_ring;
    if (monad_event_proc_import_ring(
            exec_proc, MONAD_EVENT_RING_EXEC, &exec_ring) != 0) {
        errx(
            EX_SOFTWARE,
            "monad_event_proc_import_ring failed: %s",
            monad_event_proc_get_last_error());
    }

    // Read events from the imported ring until SIGINT or the monad process
    // exits (which we assume has happened when the connection closes)
    event_loop(exec_ring, stdout);

    // The imported rings are reference counted, starting with reference count
    // of 1 upon creation. We are in charge of releasing this reference count
    // ourselves (and any other reference we may have acquired manually). We
    // must ensure that no iterators are in use before releasing the final
    // reference count on an imported ring, because when it reaches zero the
    // event ring's shared memory mappings will be pulled down.
    (void)monad_event_imported_ring_release(exec_ring);

    // Disconnect from the event process. After calling this, it is no longer
    // safe to use `exec_proc`.
    monad_event_proc_disconnect(exec_proc);
    return 0;
}
