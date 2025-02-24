/**
 * @file
 *
 * Execution event capture utility
 */

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <format>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include <err.h>
#include <signal.h>
#include <sysexits.h>

#include <CLI/CLI.hpp>

#include <monad/event/event.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_ring_db.h>

static sig_atomic_t g_should_exit = 0;

static void print_ring_db(
    char const *filename, monad_event_ring_db const *ring_db, std::FILE *out)
{
    std::fprintf(
        out,
        "ring db %s: type=%s pid=%d\n",
        filename,
        ring_db->db_data->is_snapshot ? "SNAP" : "SHM",
        ring_db->exec_pid);
    // Print the ring db entries as>
    // <ring-name> <ring-type> <online> <enabled> <capacity> <desc bytes>
    // <payload buf bytes>
    std::fprintf(
        out,
        "%-7s T S %9s %10s %10s %10s %12s %12s\n",
        "NAME",
        "CAPACITY",
        "DESC_SZ",
        "PBUF_SZ",
        "WR_SEQNO",
        "PBUF_NEXT",
        "PBUF_WIN");
    for (monad_event_ring_db_entry const &e : ring_db->db_data->rings) {
        char state_code;

        switch (e.ring_control.ring_state) {
        case MONAD_EVENT_RING_OFFLINE:
            state_code = 'X';
            break;
        case MONAD_EVENT_RING_CONFIGURED:
            state_code = 'C';
            break;
        case MONAD_EVENT_RING_ENABLED:
            state_code = 'E';
            break;
        default:
            state_code = '?';
            break;
        }

        std::fprintf(
            out,
            "%-7s %hhu %c %9lu %10lu %10lu %10lu %12lu %12lu\n",
            e.ring_name,
            e.ring_type,
            state_code,
            e.ring_capacity,
            e.ring_capacity * sizeof(monad_event_descriptor),
            e.payload_buf_size,
            __atomic_load_n(&e.ring_control.last_seqno, __ATOMIC_ACQUIRE),
            __atomic_load_n(
                &e.ring_control.next_payload_byte, __ATOMIC_ACQUIRE),
            __atomic_load_n(
                &e.ring_control.buffer_window_start, __ATOMIC_ACQUIRE));
    }
}

static void hexdump_event_payload(
    monad_event_iterator const *iter, monad_event_descriptor const *event,
    std::FILE *out)
{
    // Large thread_locals will cause a stack overflow, so make the
    // thread-local a pointer to a dynamic buffer
    constexpr size_t hexdump_buf_size = 1UL << 25;
    thread_local static std::unique_ptr<char[]> const hexdump_buf{
        new char[hexdump_buf_size]};

    std::byte const *payload_base =
        static_cast<std::byte const *>(monad_event_payload_peek(iter, event));
    std::byte const *const payload_end = payload_base + event->length;
    char *o = hexdump_buf.get();
    for (std::byte const *line = payload_base; line < payload_end; line += 16) {
        // Print one line of the dump, which is 16 bytes, in the form:
        // <offset> <8 bytes> <8 bytes>
        o = std::format_to(o, "{:#08x} ", line - payload_base);
        for (uint8_t b = 0; b < 16 && line + b < payload_end; ++b) {
            o = std::format_to(o, "{:02x}", std::to_underlying(line[b]));
            if (b == 7) {
                *o++ = ' '; // Extra padding after 8 bytes
            }
        }
        *o++ = '\n';

        // Every 512 bytes, check if the payload page data is still valid; the
        // + 16 bias is to prevent checking the first iteration
        if ((line - payload_base + 16) % 512 == 0 &&
            !monad_event_payload_check(iter, event)) {
            break; // Escape to the end, which checks the final time
        }
    }

    if (!monad_event_payload_check(iter, event)) {
        std::fprintf(stderr, "ERROR: event %lu payload lost!\n", event->seqno);
    }
    else {
        std::fwrite(
            hexdump_buf.get(),
            static_cast<size_t>(o - hexdump_buf.get()),
            1,
            out);
    }
}

static void print_event(
    monad_event_iterator *iter, monad_event_descriptor const *event,
    monad_event_thread_info const *thr_info,
    monad_event_block_exec_header const *block_exec_header, bool dump_payload,
    std::FILE *out)
{
    using std::chrono::seconds, std::chrono::nanoseconds;
    static std::chrono::sys_time<seconds> last_second{};
    static std::chrono::sys_time<nanoseconds> last_second_nanos;

    char event_buf[256];
    char time_buf[32];

    monad_event_metadata const &event_md = g_monad_event_metadata[event->type];

    std::chrono::sys_time<nanoseconds> const event_time{
        nanoseconds{event->epoch_nanos}};

    // An optimization to only do the string formatting of the %H:%M:%S part
    // of the time each second when it changes; this is a slow operation
    if (auto const cur_second = std::chrono::floor<seconds>(event_time);
        cur_second != last_second) {
        // The below should, but std::format formats the local time in the
        // UTC zone
        std::chrono::zoned_time const event_time_tz{
            std::chrono::current_zone(), cur_second};
        *std::format_to(time_buf, "{:%T}", event_time_tz) = '\0';
        last_second = cur_second;
        last_second_nanos =
            std::chrono::time_point_cast<nanoseconds>(last_second);
    }

    // Print a summary line of this event
    // <HH:MM::SS.nanos> <event-c-name> [<event-type> <event-type-hex>]
    //     SEQ: <sequence-no> LEN: <payload-length>
    //     SRC: <source-id> [<thread-name> <thread-id>]
    char *o = std::format_to(
        event_buf,
        "{}.{:09}: {} [{} {:#x}] SEQ: {} LEN: {} SRC: {} [{} ({})]",
        time_buf,
        (event_time - last_second_nanos).count(),
        event_md.c_name,
        std::to_underlying(event->type),
        std::to_underlying(event->type),
        event->seqno,
        event->length,
        event->source_id,
        thr_info->thread_name,
        thr_info->thread_id);
    if (!event->inline_payload) {
        o = std::format_to(o, " BUF_OFF: {}", event->payload_buf_offset);
    }
    if (event->block_flow_id) {
        o = std::format_to(
            o,
            " BLK: {} [CSN: {}]",
            block_exec_header->number,
            block_exec_header->consensus_seqno);
    }
    if (event->txn_id != 0) {
        o = std::format_to(o, " TXN: {}", event->txn_id - 1);
    }
    *o++ = '\n';
    std::fwrite(event_buf, static_cast<size_t>(o - event_buf), 1, out);

    if (dump_payload) {
        hexdump_event_payload(iter, event, out);
    }
}

// The "follow thread" behaves like `tail -f`: it pulls events from the ring
// and writes them to a std::FILE* as fast as possible
static void follow_thread_main(
    monad_event_ring_db const *ring_db,
    std::span<monad_event_ring const *> imported_rings,
    std::optional<uint64_t> start_seqno, bool dump_payload, std::FILE *out)
{
    monad_event_descriptor event;
    std::array<monad_event_iterator, MONAD_EVENT_RING_COUNT> iter_bufs{};
    std::span<monad_event_iterator> const iters =
        std::span{iter_bufs}.first(size(imported_rings));
    size_t not_ready_count = 0;

    monad_event_thread_info const *thread_table = ring_db->db_data->thread_info;
    monad_event_block_exec_header const *block_header_table =
        ring_db->db_data->block_headers;

    for (size_t i = 0; auto const *event_ring : imported_rings) {
        monad_event_iterator_init(&iters[i++], event_ring);
        if (start_seqno) {
            // TODO(ken): if we actually had more than one ring, would need
            //   to set this on the right one. In practice it's only used
            //   for debugging tasks starting from zero.
            iters.back().read_last_seqno = *start_seqno;
        }
    }
    while (g_should_exit == 0) {
        for (auto &iter : iters) {
            switch (monad_event_iterator_try_next(&iter, &event)) {
            case MONAD_EVENT_NOT_READY:
                if ((not_ready_count++ & ((1U << 20) - 1)) == 0) {
                    std::fflush(out);
                    if (!monad_event_ring_db_is_alive(ring_db)) {
                        g_should_exit = 1;
                    }
                }
                continue; // Nothing produced yet

            case MONAD_EVENT_GAP:
                std::fprintf(
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
                std::unreachable(); // Never returned by the zero-copy API
            }
            print_event(
                &iter,
                &event,
                &thread_table[event.source_id],
                &block_header_table[event.block_flow_id],
                dump_payload,
                out);
        }
    }
}

int main(int argc, char **argv)
{
    std::string shm_name = MONAD_EVENT_DEFAULT_RING_DB_SHM_NAME;
    std::thread follow_thread;
    bool list = false;
    bool follow = false;
    bool hexdump = false;
    std::optional<uint64_t> start_seqno;

    CLI::App cli{"monad event capture tool"};
    cli.add_option("-s,--shm-name", shm_name, "shm_open name for event ring db")
        ->capture_default_str();
    cli.add_flag("-L,--list", list, "list entries in ring db");
    cli.add_flag(
        "-f,--follow", follow, "stream events to stdout, as in tail -f");
    cli.add_flag("-H,--hex", hexdump, "hexdump event payloads in follow mode");
    cli.add_option(
        "--start-seqno",
        start_seqno,
        "force the starting sequence number to a particular value (for debug)");

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(cli.exit(e));
    }
    catch (CLI::ParseError const &e) {
        std::exit(cli.exit(e));
    }

    monad_event_ring_db ring_db;
    if (monad_event_ring_db_open(&ring_db, shm_name.c_str()) != 0) {
        errx(
            EX_SOFTWARE,
            "event library error -- %s",
            monad_event_ring_db_get_last_error());
    }

    if (list) {
        print_ring_db(shm_name.c_str(), &ring_db, stdout);
    }

    monad_event_ring event_rings[MONAD_EVENT_RING_COUNT] = {};
    std::vector<monad_event_ring const *> imported_rings;
    for (auto ring_type : {MONAD_EVENT_RING_EXEC}) {
        if (monad_event_ring_db_import(
                &ring_db, ring_type, &event_rings[ring_type]) != 0) {
            errx(
                EX_SOFTWARE,
                "event library error -- %s",
                monad_event_ring_db_get_last_error());
        }
        imported_rings.emplace_back(&event_rings[ring_type]);
    }

    if (follow) {
        follow_thread = std::thread{
            follow_thread_main,
            &ring_db,
            std::span{imported_rings},
            start_seqno,
            hexdump,
            stdout};
    }

    if (follow_thread.joinable()) {
        follow_thread.join();
    }

    for (auto &r : event_rings) {
        monad_event_ring_unmap(&r);
    }
    monad_event_ring_db_close(&ring_db);
    return 0;
}
