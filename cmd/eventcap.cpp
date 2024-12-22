/**
 * @file
 *
 * Execution event capture utility
 */

#include <algorithm>
#include <array>
#include <atomic>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <thread>
#include <utility>

#include <err.h>
#include <signal.h>
#include <sysexits.h>

#include <CLI/CLI.hpp>

#include <monad/event/event.h>
#include <monad/event/event_client.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>

namespace fs = std::filesystem;

static sig_atomic_t g_should_exit = 0;

constexpr bool is_txn_event(monad_event_type type)
{
    switch (type) {
    case MONAD_EVENT_TXN_START:
        [[fallthrough]];
    case MONAD_EVENT_TXN_LOG:
        [[fallthrough]];
    case MONAD_EVENT_TXN_RESTART:
        [[fallthrough]];
    case MONAD_EVENT_TXN_END:
        return true;

    default:
        return false;
    }
}

static void hexdump_event_payload(
    std::span<std::byte const> payload, uint64_t event_seqno,
    std::atomic<uint64_t> const *page_seqno_overwrite, std::FILE *out)
{
    // Large thread_locals will cause a stack overflow, so make the
    // thread-local a pointer to a dynamic buffer
    constexpr size_t hexdump_buf_size = 1UL << 25;
    thread_local static std::unique_ptr<char[]> const hexdump_buf{
        new char[hexdump_buf_size]};

    std::byte const *const payload_base = data(payload);
    std::byte const *const payload_end = payload_base + size(payload);
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
            page_seqno_overwrite->load(std::memory_order::acquire) >
                event_seqno) {
            break; // Escape to the end, which checks the final time
        }
    }

    if (page_seqno_overwrite->load(std::memory_order::acquire) > event_seqno) {
        std::fprintf(out, "ERROR: event %lu payload lost!\n", event_seqno);
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
    monad_event_block_exec_header const *block_exec_header, std::FILE *out)
{
    using std::chrono::nanoseconds;
    char event_buf[256];

    monad_event_metadata const &event_md = g_monad_event_metadata[event->type];

    std::chrono::sys_time<nanoseconds> const event_time{
        nanoseconds{event->epoch_nanos}};
    std::chrono::zoned_time const event_time_tz{
        std::chrono::current_zone(), event_time};

    // Print a summary line of this event
    // <HH:MM::SS.nanos> <event-c-name> [<event-type> <event-type-hex>]
    //     SEQ: <sequence-no> LEN: <payload-length>
    //     SRC: <source-id> [<thread-name> <thread-id>]
    uint64_t const seqno = event->seqno.load(std::memory_order_relaxed);
    uint64_t const length = event->length;
    char *o = std::format_to(
        event_buf,
        "{:%H:%M:%S}: {} [{} {:#x}] SEQ: {} LEN: {} SRC: {} [{} ({})]",
        event_time_tz,
        event_md.c_name,
        std::to_underlying(event->type),
        std::to_underlying(event->type),
        seqno,
        length,
        event->source_id,
        thr_info->thread_name,
        thr_info->thread_id);
    if (event->block_flow_id) {
        o = std::format_to(
            o,
            " BLK: {} [R: {}]",
            block_exec_header->number,
            block_exec_header->round);
    }
    if (is_txn_event(event->type)) {
        o = std::format_to(o, " TXN: {}", event->txn_num);
    }
    *o++ = '\n';

    // NOTE: we load the payload pointer now, because it will no longer be
    // safe to touch `event` again after calling `monad_event_reader_advance`,
    // unless we manually acquire-load `event->seqno` and compare it against
    // `seqno`
    std::atomic<uint64_t> const *page_seqno_overwrite;
    std::byte const *payload = static_cast<std::byte const *>(
        monad_event_payload_peek(iter, event, &page_seqno_overwrite));
    if (monad_event_iterator_advance(iter)) {
        std::fwrite(event_buf, static_cast<size_t>(o - event_buf), 1, out);
    }
    else {
        // Zero-copy buffer changed underneath us; the payload is gone too.
        // Note we use `last_seqno + 1` here, as even the relaxed `seqno` load
        // above is potentially not right (it could show the overwrite value)
        std::fprintf(
            out,
            "ERROR: event %lu lost during copy-out\n",
            iter->last_seqno + 1);
        return;
    }

    hexdump_event_payload({payload, length}, seqno, page_seqno_overwrite, out);
}

// The "follow thread" behaves like `tail -f`: it pulls events from the ring
// and writes them to a std::FILE* as fast as possible
static void follow_thread_main(
    std::span<monad_event_imported_ring *const> imported_rings,
    monad_event_thread_info const *thread_table,
    monad_event_block_exec_header const *block_header_table,
    std::optional<uint64_t> start_seqno, std::FILE *out)
{
    monad_event_descriptor const *event;
    monad_event_proc const *const proc = imported_rings.front()->proc;
    std::array<monad_event_iterator, MONAD_EVENT_RING_COUNT> iter_bufs{};
    std::span<monad_event_iterator> const iters =
        std::span{iter_bufs}.first(size(imported_rings));
    size_t not_ready_count = 0;

    for (size_t i = 0; auto *import : imported_rings) {
        if (monad_event_imported_ring_init_iter(import, &iters[i++]) != 0) {
            errx(
                EX_SOFTWARE,
                "monad_event_imported_ring_init_iter of %hhu failed: %s",
                import->type,
                monad_event_proc_get_last_error());
        }
        if (start_seqno) {
            // TODO(ken): if we actually had more than one ring, would need
            //   to set this on the right one. In practice it's only used
            //   for debugging tasks starting from zero.
            iters.back().last_seqno = *start_seqno;
        }
    }
    while (g_should_exit == 0) {
        for (auto &iter : iters) {
            switch (monad_event_iterator_peek(&iter, &event)) {
            case MONAD_EVENT_NOT_READY:
                if ((not_ready_count++ & ((1U << 20) - 1)) == 0) {
                    std::fflush(out);
                    if (!monad_event_proc_is_connected(proc)) {
                        g_should_exit = 1;
                    }
                }
                continue; // Nothing produced yet

            case MONAD_EVENT_GAP:
                fprintf(
                    out,
                    "event gap from %lu -> %lu, resetting\n",
                    iter.last_seqno,
                    event->seqno.load(std::memory_order_relaxed));
                monad_event_iterator_reset(&iter);
                continue;

            case MONAD_EVENT_READY:
                break; // Handled in the main loop body

            case MONAD_EVENT_PAYLOAD_EXPIRED:
                std::unreachable(); // Never returned by the zero-copy API
            }
            not_ready_count = 0;
            print_event(
                &iter,
                event,
                &thread_table[event->source_id],
                &block_header_table[event->block_flow_id],
                out);
        }
    }
}

int main(int argc, char **argv)
{
    fs::path server_socket_file = MONAD_EVENT_DEFAULT_SOCKET_PATH;
    std::thread follow_thread;
    bool follow = false;
    std::optional<uint64_t> start_seqno;
    monad_event_connect_options connect_opts{};

    // By default, failure to respond within 1 second means we assume the
    // server is dead
    connect_opts.socket_timeout.tv_sec = 1;

    CLI::App cli{"monad event capture tool"};
    cli.add_option(
           "-s,--server", server_socket_file, "path to the server socket file")
        ->capture_default_str();
    cli.add_flag(
        "-f,--follow", follow, "stream events to stdout, as in tail -f");
    cli.add_option(
           "--timeout",
           connect_opts.socket_timeout.tv_sec,
           "server socket timeout, in seconds; zero disables")
        ->capture_default_str();
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

    monad_event_proc *exec_proc;
    int connect_rc;
    // Note the comma operator because c_str() is only temporary
    connect_opts.socket_path = server_socket_file.c_str(),
    connect_rc = monad_event_proc_connect(&connect_opts, &exec_proc);
    if (connect_rc) {
        errx(
            EX_SOFTWARE,
            "monad_event_proc_connect failed: %s",
            monad_event_proc_get_last_error());
    }

    std::array<monad_event_imported_ring *, MONAD_EVENT_RING_COUNT>
        imported_rings{};
    monad_event_thread_info const *thread_table = exec_proc->thread_table;
    monad_event_block_exec_header const *block_header_table =
        exec_proc->block_header_table;
    for (auto ring_type : {MONAD_EVENT_RING_EXEC}) {
        if (monad_event_proc_import_ring(
                exec_proc, MONAD_EVENT_RING_EXEC, &imported_rings[ring_type]) !=
            0) {
            errx(
                EX_SOFTWARE,
                "monad_event_proc_import_ring of %hhu failed: %s",
                ring_type,
                monad_event_proc_get_last_error());
        }
    }

    if (follow) {
        follow_thread = std::thread{
            follow_thread_main,
            std::span{imported_rings}.first(1),
            thread_table,
            block_header_table,
            start_seqno,
            stdout};
    }

    if (follow_thread.joinable()) {
        follow_thread.join();
    }

    for (monad_event_imported_ring *const i : imported_rings) {
        (void)monad_event_imported_ring_release(i);
    }
    (void)monad_event_proc_disconnect(exec_proc);
    return 0;
}
