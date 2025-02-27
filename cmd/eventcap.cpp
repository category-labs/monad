/**
 * @file
 *
 * Execution event capture utility
 */

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

#include <alloca.h>
#include <err.h>
#include <poll.h>
#include <signal.h>
#include <sysexits.h>

#include <CLI/CLI.hpp>

#include <monad/event/event.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>

static sig_atomic_t g_should_exit = 0;

static bool process_has_exited(int pidfd)
{
    pollfd pfd = {.fd = pidfd, .events = POLLIN};
    return poll(&pfd, 1, 0) == -1 || (pfd.revents & POLLIN) == POLLIN;
}

static void print_event_ring_header(
    char const *filename, monad_event_ring_header const *h, std::FILE *out)
{
    std::fprintf(
        out,
        "event ring %s: type=%s pid=%d\n",
        filename,
        h->is_discovery ? "DISCOVERY" : "HUGE",
        h->writer_pid);
    // Print the ring db entries as>
    // <enabled> <capacity> <desc bytes> <payload buf bytes>
    //    <last write seqno> <next payload buf byte> <pbuf window start>
    std::fprintf(
        out,
        "E %9s %10s %10s %12s %14s %14s\n",
        "CAPACITY",
        "DESC_SZ",
        "PBUF_SZ",
        "WR_SEQNO",
        "PBUF_NEXT",
        "PBUF_WIN");
    std::fprintf(
        out,
        "%c %9lu %10lu %10lu %12lu %14lu %14lu\n",
        h->control.enabled ? 'Y' : 'N',
        h->ring_capacity,
        h->ring_capacity * sizeof(monad_event_descriptor),
        h->payload_buf_size,
        __atomic_load_n(&h->control.last_seqno, __ATOMIC_ACQUIRE),
        __atomic_load_n(&h->control.next_payload_byte, __ATOMIC_ACQUIRE),
        __atomic_load_n(&h->control.buffer_window_start, __ATOMIC_ACQUIRE));
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
    bool dump_payload, std::FILE *out)
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
    char *o = std::format_to(
        event_buf,
        "{}.{:09}: {} [{} {:#x}] SEQ: {} LEN: {}",
        time_buf,
        (event_time - last_second_nanos).count(),
        event_md.c_name,
        std::to_underlying(event->type),
        std::to_underlying(event->type),
        event->seqno,
        event->length);
    if (!event->inline_payload) {
        o = std::format_to(o, " BUF_OFF: {}", event->payload_buf_offset);
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
    std::span<monad_event_ring const> event_rings, int pidfd,
    std::optional<uint64_t> start_seqno, bool dump_payload, std::FILE *out)
{
    monad_event_descriptor event;
    monad_event_iterator *iter_bufs = static_cast<monad_event_iterator *>(
        alloca(sizeof(monad_event_iterator) * size(event_rings)));
    std::span<monad_event_iterator> const iters =
        std::span{iter_bufs, size(event_rings)};
    size_t not_ready_count = 0;

    for (size_t i = 0; auto const &event_ring : event_rings) {
        monad_event_iterator_init(&iters[i++], &event_ring);
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
                    if (process_has_exited(pidfd)) {
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
            print_event(&iter, &event, dump_payload, out);
        }
    }
}

int main(int argc, char **argv)
{
    std::thread follow_thread;
    bool print_header = false;
    bool follow = false;
    bool hexdump = false;
    std::vector<std::string> event_ring_paths;
    std::optional<uint64_t> start_seqno;

    CLI::App cli{"monad event capture tool"};
    cli.add_flag("--header", print_header, "print event ring file header");
    cli.add_flag(
        "-f,--follow", follow, "stream events to stdout, as in tail -f");
    cli.add_flag("-H,--hex", hexdump, "hexdump event payloads in follow mode");
    cli.add_option(
        "--start-seqno",
        start_seqno,
        "force the starting sequence number to a particular value (for debug)");
    cli.add_option(
           "event-ring-path",
           event_ring_paths,
           "path to an event ring shared memory file")
        ->default_val(MONAD_EVENT_DEFAULT_EXEC_EVENT_RING_PATH);

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(cli.exit(e));
    }
    catch (CLI::ParseError const &e) {
        std::exit(cli.exit(e));
    }

    std::vector<monad_event_ring> event_rings;
    int pidfd = -1;
    for (auto const &path : event_ring_paths) {
        monad_event_ring &r = event_rings.emplace_back();
        int *const pfd = pidfd == -1 ? &pidfd : nullptr;
        if (monad_event_ring_map(&r, path.c_str(), pfd) != 0) {
            errx(
                EX_SOFTWARE,
                "event library error -- %s",
                monad_event_ring_get_last_error());
        }
        if (print_header) {
            print_event_ring_header(path.c_str(), r.header, stdout);
        }
    }

    if (follow) {
        follow_thread = std::thread{
            follow_thread_main,
            std::span{event_rings},
            pidfd,
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
    return 0;
}
