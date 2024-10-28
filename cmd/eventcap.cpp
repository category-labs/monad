#include <algorithm>
#include <atomic>
#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <latch>
#include <memory>
#include <span>
#include <string>
#include <thread>
#include <utility>

#include <err.h>
#include <errno.h>
#include <sysexits.h>

#include <CLI/CLI.hpp>

#include <monad/event/event.h>
#include <monad/event/event_consumer.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_shmem.h>

namespace fs = std::filesystem;

static monad_event_thread_info g_missing_thread_info = {
    .thread_id = 0, .source_id = 0, .thread_name = "<unknown thread name>"};

static void print_event(
    monad_event_queue const *queue, monad_event_descriptor const &event,
    monad_event_thread_info const *thr_info, std::FILE *out)
{
    using std::chrono::nanoseconds;
    constexpr size_t payload_buf_size = 1UL << 23;
    char event_buf[256];
    // Large thread_locals will cause a stack overflow, so make the
    // thread-local a pointer to a dynamic buffer
    thread_local static std::unique_ptr<char[]> const payload_buf{
        new char[payload_buf_size]};
    monad_event_domain const domain = MONAD_EVENT_DOMAIN(event.type);
    monad_event_domain_metadata const &domain_md =
        g_monad_event_domain_meta[domain];
    monad_event_metadata const &event_md =
        domain_md.event_meta[MONAD_EVENT_DRCODE(event.type)];
    if (thr_info == nullptr) {
        thr_info = &g_missing_thread_info;
    }

    std::chrono::sys_time<nanoseconds> const event_time{
        nanoseconds{event.epoch_nanos}};
    std::chrono::zoned_time const event_time_tz{
        std::chrono::current_zone(), event_time};

    // Copy the event payload locally before it gets overwritten
    size_t const copy_size = std::min<size_t>(event.length, payload_buf_size);
    std::byte const *const payload = static_cast<std::byte const *>(
        monad_event_memcpy(queue, &event, payload_buf.get(), copy_size));
    std::byte const *const payload_end = payload + copy_size;

    // Print a summary line of this event
    // <HH:MM::SS.nanos> <domain-name>:<event-c-name> [<domain-code>:<dr-code>
    //     <event-type-hex>] SEQ: <sequence-no> LEN: <payload-length> SRC:
    //     <source-id> [<thread-name> <thread-id>]
    char *o = std::format_to(
        event_buf,
        "{:%H:%M:%S}: {}:{} [{}:{} {:#x}] SEQ: {} LEN: {} SRC: {} [{} ({})]",
        event_time_tz,
        domain_md.name,
        event_md.c_name,
        std::to_underlying(domain),
        MONAD_EVENT_DRCODE(event.type),
        std::to_underlying(event.type),
        event.seqno,
        event.length,
        event.source_id,
        thr_info->thread_name,
        thr_info->thread_id);
    *o++ = '\n';
    *o++ = '\0';
    std::fwrite(event_buf, static_cast<size_t>(o - event_buf - 1), 1, out);

    // Print a hexdump of the event payload
    for (std::byte const *line = payload; line < payload_end; line += 16) {
        // Print one line of the dump, which is 16 bytes, in the form:
        // <offset> <8 bytes> - <8 bytes>
        std::fprintf(out, "%p", line);
        for (uint8_t b = 0; b < 16 && line + b < payload_end; ++b) {
            std::fprintf(out, " %02hhx", std::to_underlying(line[b]));
            if (b == 7) {
                std::fprintf(out, " -"); // Extra padding after 8 bytes
            }
        }
        std::fprintf(out, "\n");
    }
}

// The "follow thread" behaves like `tail -f`: it pulls events from the queue
// and writes them to a std::FILE* as fast as possible
static void
follow_thread_main(monad_event_queue *queue, std::latch *latch, std::FILE *out)
{
    monad_event_descriptor events[64];
    size_t npolls = 0;
    monad_event_thread_info *thread_info[256] = {};
    std::atomic<uint32_t> *page_generation;

    latch->arrive_and_wait();
    while (true) {
        size_t const num_events =
            monad_event_poll(queue, events, std::size(events), nullptr);
        for (monad_event_descriptor const &e : std::span{events, num_events}) {
            if (e.type == MONAD_EVENT_THREAD_CREATE) {
                monad_event_mempeek(
                    queue,
                    &e,
                    std::bit_cast<void **>(&thread_info[e.source_id]),
                    &page_generation);
            }
            print_event(queue, e, thread_info[e.source_id], out);
        }
        if ((npolls++ & ((1U << 23) - 1)) == 0) {
            if (!monad_event_queue_is_connected(queue)) {
                break;
            }
            std::fflush(out);
        }
    }
    monad_event_queue_destroy(queue);
}

static int print_domains(char const *socket_path)
{
    monad_event_queue_options const queue_opts = {.socket_path = socket_path};
    monad_event_queue *queue;
    uint64_t available_domains;
    // Connect to the server and retrieve its recording domain mask.
    if (monad_event_queue_create(&queue_opts, &queue) != 0) {
        errx(
            EX_SOFTWARE,
            "monad_event_create_queue failed: %s",
            monad_event_get_last_error());
    }
    if (monad_event_queue_set_domain_mask(
            queue, 0, &available_domains, nullptr, nullptr) != 0) {
        errx(
            EX_SOFTWARE,
            "monad_event_queue_set_domain_mask failed: %s",
            monad_event_get_last_error());
    }
    std::fprintf(
        stdout,
        "server has %u domains enabled\n",
        std::popcount(available_domains));
    if (available_domains != 0) {
        std::fprintf(
            stdout,
            "##. %-16s %3s %10s DESCRIPTION\n",
            "NAME",
            "ID",
            "HEX_MASK");
    }
    unsigned n_domains = 0;
    while (available_domains != 0) {
        unsigned const domain = std::countr_zero(available_domains) + 1;
        available_domains &= ~MONAD_EVENT_DOMAIN_MASK(domain);
        if (domain >= g_monad_event_domain_meta_size ||
            g_monad_event_domain_meta[domain].domain ==
                MONAD_EVENT_DOMAIN_NONE) {
            continue;
        }
        std::fprintf(
            stdout,
            "%02u. %-16s %3hhu [%08lx] %s\n",
            ++n_domains,
            g_monad_event_domain_meta[domain].name,
            domain,
            MONAD_EVENT_DOMAIN_MASK(domain),
            g_monad_event_domain_meta[domain].description);
    }
    return 0;
}

int main(int argc, char **argv)
{
    fs::path server_socket_file = MONAD_EVENT_DEFAULT_SOCKET_PATH;
    std::thread follow_thread;
    std::string domain_enable_mask_input = "all";
    std::string domain_disable_mask_input = "none";
    bool follow = false;
    bool list_domains = false;
    monad_event_queue_options queue_opts{};

    // By default, failure to respond within 1 second means we assume the
    // server is dead
    queue_opts.socket_timeout.tv_sec = 1;

    CLI::App cli{"monad event capture tool"};
    cli.add_option(
           "-s,--server", server_socket_file, "path to the server socket file")
        ->capture_default_str();
    cli.add_flag(
        "-f,--follow", follow, "stream events to stdout, as in tail -f");
    cli.add_option(
           "-d,--domains",
           domain_enable_mask_input,
           "comma-separated list of domains to enable, or `all`")
        ->capture_default_str();
    cli.add_option(
           "-D,--remove-domains",
           domain_disable_mask_input,
           "comma-separated list of domains to disable, or `none`")
        ->capture_default_str();
    cli.add_flag(
        "-L,--list-domains",
        list_domains,
        "lists event domains enabled in the server");
    cli.add_option(
        "-R,--ring-shift",
        queue_opts.ring_shift,
        "size of event descriptor ring, expressed as a power-of-2 exponent");
    cli.add_option(
           "--timeout",
           queue_opts.socket_timeout.tv_sec,
           "server socket timeout, in seconds; zero disables")
        ->capture_default_str();

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(cli.exit(e));
    }
    catch (CLI::ParseError const &e) {
        std::exit(cli.exit(e));
    }

    if (list_domains) {
        // -L lists the domains active in the server, then exits
        return print_domains(server_socket_file.c_str());
    }

    uint64_t domain_enable_mask;
    if (int const rc = monad_event_parse_domain_mask(
            domain_enable_mask_input.c_str(), &domain_enable_mask)) {
        errno = rc;
        err(EX_USAGE,
            "unable to parse domain enable mask `%s`",
            domain_enable_mask_input.c_str());
    }
    uint64_t domain_disable_mask;
    if (int const rc = monad_event_parse_domain_mask(
            domain_disable_mask_input.c_str(), &domain_disable_mask)) {
        errno = rc;
        err(EX_USAGE,
            "unable to parse domain disable mask `%s`",
            domain_disable_mask_input.c_str());
    }
    if (follow) {
        int queue_rc;
        monad_event_queue *queue;
        // Note the comma operator because c_str() is only temporary
        queue_opts.socket_path = server_socket_file.c_str(),
        queue_rc = monad_event_queue_create(&queue_opts, &queue);
        if (queue_rc != 0) {
            errx(
                EX_SOFTWARE,
                "monad_event_create_queue failed: %s",
                monad_event_get_last_error());
        }

        uint64_t const desired_mask = domain_enable_mask & ~domain_disable_mask;
        std::latch start_latch{2};
        follow_thread =
            std::thread{follow_thread_main, queue, &start_latch, stdout};

        // Wait until the thread is ready to start spinning before changing
        // the queue's domain mask; this prevents us from gapping immediately
        start_latch.arrive_and_wait();
        if (int const rc = monad_event_queue_set_domain_mask(
                queue, desired_mask, nullptr, nullptr, nullptr)) {
            errno = rc;
            err(EX_SOFTWARE, "unable to set domain mask to %lx", desired_mask);
        }
    }

    if (follow_thread.joinable()) {
        follow_thread.join();
    }
    return 0;
}
