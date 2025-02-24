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
#include <getopt.h>
#include <signal.h>
#include <sysexits.h>
#include <time.h>

#include <monad/event/event.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_ring_db.h>

static void usage(FILE *out)
{
    extern char const *__progname;
    fprintf(out, "usage: %s [-h] [<shm-name>]\n", __progname);
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
"  <shm-name>    name of execution daemon's ring db shared memory object\n"
"                  [default: %s]\n",
    MONAD_EVENT_DEFAULT_RING_DB_SHM_NAME);
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
    static char time_buf[32];
    static time_t last_second = 0;

    ldiv_t time_parts;
    char event_buf[256];
    char *o = event_buf;

    struct monad_event_metadata const *event_md =
        &g_monad_event_metadata[event->type];

    // An optimization to only do the string formatting of the %H:%M:%S part
    // of the time each second when it changes, because strftime(3) is slow
    time_parts = ldiv(event->epoch_nanos, 1'000'000'000L);
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
    //     SRC: <source-id> [<thread-name> <thread-id>]
    o += sprintf(
        event_buf,
        "%s.%09ld: %s [%hu 0x%hx] SEQ: %lu LEN: %u SRC: %u [%s (%lu)]",
        time_buf,
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
    if (event->txn_id != 0) {
        o += sprintf(o, " TXN: %u", event->txn_id - 1);
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
static void event_loop(
    struct monad_event_ring_db const *ring_db,
    struct monad_event_ring const *event_ring, FILE *out)
{
    struct monad_event_descriptor event;
    struct monad_event_iterator iter;
    struct monad_event_thread_info const *const thread_table =
        ring_db->db_data->thread_info;
    struct monad_event_block_exec_header const *const block_header_table =
        ring_db->db_data->block_headers;
    uint64_t not_ready_count = 0;

    monad_event_iterator_init(&iter, event_ring);
    while (g_should_stop == 0) {
        switch (monad_event_iterator_try_next(&iter, &event)) {
        case MONAD_EVENT_NOT_READY:
            if ((not_ready_count++ & ((1U << 20) - 1)) == 0) {
                fflush(out);
                if (!monad_event_ring_db_is_alive(ring_db)) {
                    g_should_stop = 1;
                }
            }
            continue; // Nothing produced yet

        case MONAD_EVENT_GAP:
            fprintf(
                stderr,
                "ERROR: event gap from %lu -> %lu, resetting\n",
                iter.read_last_seqno,
                __atomic_load_n(iter.write_last_seqno, __ATOMIC_ACQUIRE));
            monad_event_iterator_reset(&iter);
            not_ready_count = 0;
            continue;

        case MONAD_EVENT_SUCCESS:
            not_ready_count = 0;
            break; // Handled in the main loop body

        case MONAD_EVENT_PAYLOAD_EXPIRED:
            unreachable(); // Never returned by monad_event_iterator_try_next
        }
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
    char *shm_name = MONAD_EVENT_DEFAULT_RING_DB_SHM_NAME;
    int const pos_arg_idx = parse_options(argc, argv);
    if (argc - pos_arg_idx > 1) {
        usage(stderr);
        return EX_USAGE;
    }
    if (pos_arg_idx + 1 == argc) {
        shm_name = argv[pos_arg_idx];
    }
    signal(SIGINT, handle_signal);

    // We start by opening a handle to an event ring database (referred to as
    // the "ring db"). This is a shared memory object managed by a running
    // execution daemon that provides metadata about which event rings are
    // available
    struct monad_event_ring_db ring_db;
    if (monad_event_ring_db_open(&ring_db, shm_name) != 0) {
        // Our error message doesn't need to state what failed (i.e., we don't
        // need to mention `monad_event_ring_db_open` in the error message)
        // because the library's error system includes this
        errx(
            EX_SOFTWARE,
            "event library error -- %s",
            monad_event_ring_db_get_last_error());
    }

    // Check if the execution event ring is enabled
    if (ring_db.db_data->rings[MONAD_EVENT_RING_EXEC].ring_control.ring_state !=
        MONAD_EVENT_RING_ENABLED) {
        errx(
            EX_NOINPUT,
            "execution event ring is not enabled in process %d",
            ring_db.exec_pid);
    }

    // The next step is to "import" an event ring using the information in the
    // ring db. Import here means that we'll map all the ring's shared memory
    // segments into our process' address space. If this is successful, we'll
    // be able to create one or more iterators over that ring's events.
    struct monad_event_ring exec_ring;
    if (monad_event_ring_db_import(
            &ring_db, MONAD_EVENT_RING_EXEC, &exec_ring) != 0) {
        errx(
            EX_SOFTWARE,
            "event library error -- %s",
            monad_event_ring_db_get_last_error());
    }

    // Read events from the imported ring until SIGINT or the monad process
    // exits (which we assume has happened when the connection closes)
    event_loop(&ring_db, &exec_ring, stdout);

    // Clean up: unmap the execution event ring from our address space and
    // close the ring db
    monad_event_ring_unmap(&exec_ring);
    monad_event_ring_db_close(&ring_db);
    return 0;
}
