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
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <sys/mman.h>
#include <sysexits.h>
#include <unistd.h>

#include <CLI/CLI.hpp>

#include <monad/core/assert.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_ring.h>
#include <monad/event/event_ring_util.h>
#include <monad/event/test_event_types.h>

static sig_atomic_t g_should_exit = 0;

struct MetadataTableEntry
{
    uint8_t const (*hash)[32];
    std::span<monad_event_metadata const> entries;
} MetadataTable[] = {
    [MONAD_EVENT_RING_TYPE_NONE] =
        {
            nullptr,
            {},
        },
    [MONAD_EVENT_RING_TYPE_TEST] =
        {
            &g_monad_test_event_metadata_hash,
            std::span{g_monad_test_event_metadata},
        },
};

struct EventRingNameToDefaultPathEntry
{
    std::string_view name;
    char const *default_path;
} EventRingNameToDefaultPathTable[] = {
    [MONAD_EVENT_RING_TYPE_NONE] =
        {
            g_monad_event_ring_type_names[MONAD_EVENT_RING_TYPE_NONE],
            {},
        },
    [MONAD_EVENT_RING_TYPE_TEST] = {
        .name = g_monad_event_ring_type_names[MONAD_EVENT_RING_TYPE_TEST],
        .default_path = MONAD_EVENT_DEFAULT_TEST_RING_PATH}};

static char const *get_default_path_for_event_ring_name(std::string_view name)
{
    auto const i_entry = std::ranges::find(
        EventRingNameToDefaultPathTable,
        name,
        &EventRingNameToDefaultPathEntry::name);
    return i_entry != std::ranges::end(EventRingNameToDefaultPathTable)
               ? i_entry->default_path
               : nullptr;
}

struct mapped_event_ring
{
    int ring_fd;
    std::string origin_path;
    monad_event_ring event_ring;
    std::span<monad_event_metadata const> metadata_entries;
    std::optional<uint64_t> start_seqno;
};

static bool event_ring_is_abandoned(int ring_fd)
{
    pid_t writer_pids[32];
    size_t n_pids = std::size(writer_pids);
    int const rc =
        monad_event_ring_find_writer_pids(ring_fd, writer_pids, &n_pids);
    MONAD_ASSERT(rc == ENOSYS, "not implemented yet, always claim it's alive");
    return false;
}

static void print_event_ring_header(
    char const *filename, monad_event_ring_header const *h, std::FILE *out)
{
    std::fprintf(out, "event ring %s\n", filename);
    // Print the event ring file header information:
    // <type-name> [<type-code>] <descriptor capacity> <descriptor byte size>
    //    <payload buf size> <context area size> <last write seqno>
    //    <next payload buf byte> <pbuf window start>
    std::fprintf(
        out,
        "%10s %9s %10s %10s %10s %12s %14s %14s\n",
        "TYPE",
        "DESC_CAP",
        "DESC_SZ",
        "PBUF_SZ",
        "CTX_SZ",
        "WR_SEQNO",
        "PBUF_NEXT",
        "PBUF_WIN");
    std::fprintf(
        out,
        "%6s [%hu] %9lu %10lu %10lu %10lu %12lu %14lu %14lu\n",
        g_monad_event_ring_type_names[h->type],
        h->type,
        h->size.descriptor_capacity,
        h->size.descriptor_capacity * sizeof(monad_event_descriptor),
        h->size.payload_buf_size,
        h->size.context_area_size,
        __atomic_load_n(&h->control.last_seqno, __ATOMIC_ACQUIRE),
        __atomic_load_n(&h->control.next_payload_byte, __ATOMIC_ACQUIRE),
        __atomic_load_n(&h->control.buffer_window_start, __ATOMIC_ACQUIRE));
}

static void hexdump_event_payload(
    monad_event_ring const *event_ring, monad_event_descriptor const *event,
    std::FILE *out)
{
    // Large thread_locals will cause a stack overflow, so make the
    // thread-local a pointer to a dynamic buffer
    constexpr size_t hexdump_buf_size = 1UL << 25;
    thread_local static std::unique_ptr<char[]> const hexdump_buf{
        new char[hexdump_buf_size]};

    std::byte const *payload_base = static_cast<std::byte const *>(
        monad_event_ring_payload_peek(event_ring, event));
    std::byte const *const payload_end = payload_base + event->payload_size;
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
            !monad_event_ring_payload_check(event_ring, event)) {
            break; // Escape to the end, which checks the final time
        }
    }

    if (!monad_event_ring_payload_check(event_ring, event)) {
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
    monad_event_ring const *event_ring, monad_event_descriptor const *event,
    std::span<monad_event_metadata const> metadata_entries, bool dump_payload,
    std::FILE *out)
{
    using std::chrono::seconds, std::chrono::nanoseconds;
    static std::chrono::sys_time<seconds> last_second{};
    static std::chrono::sys_time<nanoseconds> last_second_nanos;
    static char time_buf[32];
    char event_buf[256];

    monad_event_metadata const &event_md = metadata_entries[event->event_type];
    std::chrono::sys_time<nanoseconds> const event_time{
        nanoseconds{event->record_epoch_nanos}};

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
        "{}.{:09}: {} [{} {:#x}] SEQ: {} LEN: {} BUF_OFF: {}",
        time_buf,
        (event_time - last_second_nanos).count(),
        event_md.c_name,
        event->event_type,
        event->event_type,
        event->seqno,
        event->payload_size,
        event->payload_buf_offset);
    *o++ = '\n';
    std::fwrite(event_buf, static_cast<size_t>(o - event_buf), 1, out);

    if (dump_payload) {
        hexdump_event_payload(event_ring, event, out);
    }
}

// The "follow thread" behaves like `tail -f`: it pulls events from the ring
// and writes them to a std::FILE* as fast as possible
static void follow_thread_main(
    std::span<mapped_event_ring const> mapped_event_rings, bool dump_payload,
    std::FILE *out)
{
    monad_event_descriptor event;
    monad_event_iterator *iter_bufs = static_cast<monad_event_iterator *>(
        alloca(sizeof(monad_event_iterator) * size(mapped_event_rings)));
    std::span<monad_event_iterator> const iters =
        std::span{iter_bufs, size(mapped_event_rings)};
    size_t not_ready_count = 0;

    for (size_t i = 0; mapped_event_ring const &mr : mapped_event_rings) {
        monad_event_ring_init_iterator(&mr.event_ring, &iters[i++]);
        if (mr.start_seqno) {
            iters.back().read_last_seqno = *mr.start_seqno;
        }
    }
    while (g_should_exit == 0) {
        for (size_t i = 0; auto &iter : iters) {
            mapped_event_ring const &mr = mapped_event_rings[i++];
            auto const event_metadata = mr.metadata_entries;
            switch (monad_event_iterator_try_next(&iter, &event)) {
            case MONAD_EVENT_NOT_READY:
                if ((not_ready_count++ & ((1U << 20) - 1)) == 0) {
                    std::fflush(out);
                    if (event_ring_is_abandoned(mr.ring_fd)) {
                        g_should_exit = 1;
                    }
                }
                continue; // Nothing produced yet

            case MONAD_EVENT_GAP:
                std::fprintf(
                    stderr,
                    "ERROR: event gap from %lu -> %lu, resetting\n",
                    iter.read_last_seqno,
                    __atomic_load_n(
                        &iter.control->last_seqno, __ATOMIC_ACQUIRE));
                monad_event_iterator_reset(&iter);
                not_ready_count = 0;
                continue;

            case MONAD_EVENT_SUCCESS:
                not_ready_count = 0;
                break; // Handled in the main loop body
            }
            print_event(
                &mr.event_ring, &event, event_metadata, dump_payload, out);
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
        ->default_val(
            g_monad_event_ring_type_names[MONAD_EVENT_RING_TYPE_TEST]);

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(cli.exit(e));
    }
    catch (CLI::ParseError const &e) {
        std::exit(cli.exit(e));
    }

    std::vector<mapped_event_ring> mapped_event_rings;
    for (auto const &path : event_ring_paths) {
        mapped_event_ring &mr = mapped_event_rings.emplace_back();

        // The "path" might actually be a standard event ring name; if it maps
        // to a default path, we'll use that instead, otherwise we'll open(2) it
        if (auto const *p = get_default_path_for_event_ring_name(path)) {
            mr.origin_path = p;
        }
        else {
            mr.origin_path = path;
        }
        mr.ring_fd = open(mr.origin_path.c_str(), O_RDONLY);
        if (mr.ring_fd == -1) {
            err(EX_CONFIG,
                "could not open event ring file `%s`",
                mr.origin_path.c_str());
        }

        bool fs_supports_hugetlb;
        if (monad_check_path_supports_map_hugetlb(
                mr.origin_path.c_str(), &fs_supports_hugetlb) != 0) {
            errx(
                EX_SOFTWARE,
                "event library error -- %s",
                monad_event_ring_get_last_error());
        }
        int const mmap_extra_flags =
            fs_supports_hugetlb ? MAP_POPULATE | MAP_HUGETLB : MAP_POPULATE;

        // Map this event ring into our address space
        if (monad_event_ring_mmap(
                &mr.event_ring,
                PROT_READ,
                mmap_extra_flags,
                mr.ring_fd,
                0,
                mr.origin_path.c_str()) != 0) {
            errx(
                EX_SOFTWARE,
                "event library error -- %s",
                monad_event_ring_get_last_error());
        }

        // Ensure it's safe to dereference `MetadataTable[ring_type]`
        monad_event_ring_type const ring_type = mr.event_ring.header->type;
        if (std::to_underlying(ring_type) >= std::size(MetadataTable)) {
            errx(
                EX_CONFIG,
                "do not have the metadata mapping for event ring `%s` type %hu",
                mr.origin_path.c_str(),
                ring_type);
        }

        // Get the metadata hash we're compiled with, or substitute the zero
        // hash if the command line told us to
        if (MetadataTable[ring_type].hash == nullptr) {
            errx(
                EX_CONFIG,
                "event ring `%s` has type %hu, but we don't know its metadata "
                "hash",
                mr.origin_path.c_str(),
                ring_type);
        }
        uint8_t const(&hash)[32] = *MetadataTable[ring_type].hash;

        // Unlike simpler tools, we should be able to work with any type
        if (monad_event_ring_check_type(&mr.event_ring, ring_type, hash) != 0) {
            errx(
                EX_SOFTWARE,
                "event library error -- %s",
                monad_event_ring_get_last_error());
        }
        mr.metadata_entries = MetadataTable[ring_type].entries;
        mr.start_seqno = start_seqno;
        if (print_header) {
            print_event_ring_header(
                mr.origin_path.c_str(), mr.event_ring.header, stdout);
        }
    }

    if (follow) {
        follow_thread = std::thread{
            follow_thread_main, std::span{mapped_event_rings}, hexdump, stdout};
    }

    if (follow_thread.joinable()) {
        follow_thread.join();
    }

    for (auto &mr : mapped_event_rings) {
        monad_event_ring_unmap(&mr.event_ring);
        (void)close(mr.ring_fd);
    }
    return 0;
}
