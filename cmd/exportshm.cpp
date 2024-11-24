/**
 * @file
 *
 * This command line utility dumps a snapshot of all the execution event shared
 * memory segments to a single file. This is only used to generate static input
 * data for test cases, which is replayed by the fake event server (see
 * event_server_test.c in libs/event).
 */

#include <atomic>
#include <bit>
#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <filesystem>

#include <err.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/socket.h>
#include <sysexits.h>
#include <unistd.h>

#include <CLI/CLI.hpp>

#include <monad/core/assert.h>
#include <monad/core/bit_util.h>
#include <monad/event/event.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_queue.h>
#include <monad/event/event_queue_internal.h>
#include <monad/event/event_reader.h>

namespace fs = std::filesystem;

struct test_file_writer
{
    int fd;
    size_t segments_written;
    size_t mmap_page_size;
};

// A test file is an array of these entries (terminated by an all-zero
// sentinel) explaining where the various other segments in the file are
// written and what they contain
struct test_file_segment
{
    uint32_t type;
    uint16_t page_id;
    uint16_t metadata_type;
    uint64_t length;
    uint64_t offset;
};

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
static size_t monad_round_size_to_align(size_t size, size_t align)
{
    MONAD_DEBUG_ASSERT(std::has_single_bit(align));
    return bit_round_up(size, static_cast<unsigned>(std::countr_zero(align)));
}

static void init_test_file_writer(test_file_writer *tfw, int fd)
{
    tfw->fd = fd;
    tfw->segments_written = 0;
    tfw->mmap_page_size = static_cast<size_t>(getpagesize());
    // Skip over the first two pages, which will hold the segment directory.
    off_t const skip = static_cast<off_t>(tfw->mmap_page_size * 2U);
    off_t o = ftruncate(tfw->fd, skip);
    MONAD_ASSERT(o != -1);
    o = lseek(tfw->fd, skip, SEEK_SET);
    MONAD_ASSERT(o != -1);
}

static void save_mmap_region(
    test_file_writer *tfw, test_file_segment *segment, void const *data,
    size_t length)
{
    // Write the segment descriptor describing the memory segment we're dumping
    segment->length = length;
    off_t curoff = lseek(tfw->fd, 0, SEEK_CUR);
    MONAD_ASSERT(curoff != -1);
    segment->offset = (uint64_t)curoff;
    ssize_t wr_bytes = pwrite(
        tfw->fd,
        segment,
        sizeof *segment,
        static_cast<off_t>(sizeof(*segment) * tfw->segments_written++));
    MONAD_ASSERT(wr_bytes == sizeof(*segment));

    // Write the segment data, and ensure we're mmap(2)-page aligned when done
    wr_bytes = write(tfw->fd, data, length);
    MONAD_ASSERT(wr_bytes == static_cast<ssize_t>(length));
    curoff += wr_bytes;
    // Round up the nearest multiple of the page size. This is a bit silly
    // as we currently force everything to be copied to HUGETLB-aligned memfds
    // anyway.
    off_t alignedoff =
        (off_t)monad_round_size_to_align((size_t)curoff, tfw->mmap_page_size);
    if (alignedoff != curoff) {
        alignedoff = ftruncate(tfw->fd, alignedoff);
        MONAD_ASSERT(alignedoff != -1);
        curoff = lseek(tfw->fd, 0, SEEK_END);
        MONAD_ASSERT(curoff != -1);
    }
}

static void close_test_file_writer(test_file_writer *tfw)
{
    test_file_segment s{};

    // The segment directory is terminated by an all zero segment (i.e.,
    // type == MONAD_EVENT_MSG_NONE) followed by the event metadata hash
    off_t const o = lseek(
        tfw->fd,
        static_cast<off_t>(sizeof(s) * tfw->segments_written),
        SEEK_SET);
    MONAD_ASSERT(o != -1);
    ssize_t wr_bytes = write(tfw->fd, &s, sizeof s);
    MONAD_ASSERT(wr_bytes == sizeof s);
    wr_bytes = write(
        tfw->fd,
        g_monad_event_metadata_hash,
        sizeof g_monad_event_metadata_hash);
    MONAD_ASSERT(wr_bytes == sizeof g_monad_event_metadata_hash);
    close(tfw->fd);
}

static void
wait_for_seqno(monad_event_queue *queue, uint64_t last_seqno, pid_t pid)
{
    std::fprintf(
        stdout,
        "waiting for pid %d to materialize seqno: %lu\n",
        pid,
        last_seqno);

    monad_event_reader r;
    monad_event_queue_ffi_extra ffi_ex;
    monad_event_queue_init_reader(queue, &r, &ffi_ex);

    // Manually rewind to the beginning
    r.last_seqno = 0;
    while (true) {
        monad_event_descriptor const *event;
        switch (monad_event_reader_peek(&r, &event)) {
        case MONAD_EVENT_GAP:
            MONAD_ABORT("unexpected gap during last_seqno wait");

        case MONAD_EVENT_PAYLOAD_EXPIRED:
            std::unreachable(); // Never actually returned by peek

        case MONAD_EVENT_NOT_READY:
            continue;

        case MONAD_EVENT_READY:
            if (auto const this_seqno =
                    event->seqno.load(std::memory_order::acquire);
                this_seqno >= last_seqno) {
                kill(pid, SIGINT);
                fprintf(
                    stdout,
                    "saw seqno: %lu, sent signal %d to pid %d\n",
                    this_seqno,
                    SIGINT,
                    pid);
                return;
            }
            monad_event_reader_advance(&r);
            break;
        }
    }
}

void export_shm_segments(
    monad_event_queue *queue, int fd,
    monad_event_thread_info const *thread_table,
    monad_event_block_exec_header const *block_header_table)
{
    test_file_writer tfw{};
    test_file_segment segment{};

    // Setup the output structure and skip over the fixed-size segment
    // descriptor table
    init_test_file_writer(&tfw, fd);

    // Write the control page
    segment.type = MONAD_EVENT_MSG_MAP_RING_CONTROL;
    save_mmap_region(
        &tfw, &segment, queue->event_ring.control, tfw.mmap_page_size);

    // Write as much of the descriptor table as has actually been written.
    uint64_t const last_seqno =
        queue->event_ring.control->prod_next.load(std::memory_order_acquire);
    monad_event_descriptor const *const last_event =
        &queue->event_ring
             .descriptor_table[last_seqno & queue->event_ring.capacity_mask];
    size_t const event_count =
        static_cast<size_t>(last_event - queue->event_ring.descriptor_table);
    segment.type = MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE;
    save_mmap_region(
        &tfw,
        &segment,
        queue->event_ring.descriptor_table,
        sizeof(*last_event) * event_count);

    // Save all the payload pages that have something recorded to them, and
    // figure out which one of them is the metadata page as we're doing this.
    monad_event_payload_page const *metadata_page = nullptr;
    segment.type = MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE;
    auto const *thread_table_u8 = std::bit_cast<uint8_t const *>(thread_table);
    auto const *block_header_table_u8 =
        std::bit_cast<uint8_t const *>(block_header_table);
    for (uint16_t p = 0; p < queue->num_payload_pages; ++p) {
        monad_event_payload_page const *page = queue->payload_pages[p];
        if (page->alloc_count == 0) {
            // Page was never used, don't allocate a segment for it
            continue;
        }
        segment.page_id = page->page_id;
        // We must be extremely careful here: the pointers inside `page` point
        // into the other process' address space, but `page` itself (and the
        // metadata tables) is mapped at a different location in our own
        // address space. The only thing we can safely do with that is compute
        // the length.
        size_t const map_len = (size_t)(page->heap_next - page->page_base);
        save_mmap_region(&tfw, &segment, page, map_len);
        if (thread_table_u8 > (uint8_t const *)page &&
            thread_table_u8 < (uint8_t const *)page + map_len) {
            MONAD_ASSERT(
                block_header_table_u8 > (uint8_t const *)page &&
                block_header_table_u8 < (uint8_t const *)page + map_len);
            metadata_page = page;
        }
    }
    MONAD_ASSERT(metadata_page != nullptr);

    // Export thread table and block table offset; we manually write these
    // metadata sections since there is no associated mmap region for them
    ssize_t wr_bytes;
    segment.type = MONAD_EVENT_MSG_METADATA_OFFSET;
    segment.page_id = metadata_page->page_id;
    segment.metadata_type = MONAD_EVENT_METADATA_THREAD;
    segment.offset = static_cast<uint64_t>(
        thread_table_u8 - std::bit_cast<uint8_t const *>(metadata_page));
    segment.length = 0;
    wr_bytes = pwrite(
        tfw.fd,
        &segment,
        sizeof(segment),
        static_cast<off_t>(sizeof(segment) * tfw.segments_written++));
    MONAD_ASSERT(wr_bytes == sizeof(segment));

    segment.metadata_type = MONAD_EVENT_METADATA_BLOCK_FLOW;
    segment.offset = static_cast<uint64_t>(
        block_header_table_u8 - std::bit_cast<uint8_t const *>(metadata_page));
    ;
    wr_bytes = pwrite(
        tfw.fd,
        &segment,
        sizeof(segment),
        static_cast<off_t>(sizeof(segment) * tfw.segments_written++));
    MONAD_ASSERT(wr_bytes == sizeof(segment));

    close_test_file_writer(&tfw);
}

int main(int argc, char **argv)
{
    fs::path server_socket_file = MONAD_EVENT_DEFAULT_SOCKET_PATH;
    fs::path output_file;
    uint64_t last_seqno;
    monad_event_queue_options queue_opts{};

    // Defaults
    queue_opts.socket_timeout.tv_sec = 1;

    CLI::App cli{"monad event export shared memory tool"};
    cli.add_option(
           "-s,--server", server_socket_file, "path to the server socket file")
        ->capture_default_str();
    cli.add_option(
           "--timeout",
           queue_opts.socket_timeout.tv_sec,
           "server socket timeout, in seconds; zero disables")
        ->capture_default_str();
    cli.add_option(
           "output",
           output_file,
           "file that shared memory segments will be exported to")
        ->required();
    cli.add_option(
           "last",
           last_seqno,
           "(approximate) last sequence number to place in the file")
        ->required();

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(cli.exit(e));
    }
    catch (CLI::ParseError const &e) {
        std::exit(cli.exit(e));
    }

    // Connect to the queue
    int queue_rc;
    monad_event_queue *queue;
    monad_event_thread_info const *thread_table;
    monad_event_block_exec_header const *block_header_table;
    queue_opts.queue_type = MONAD_EVENT_QUEUE_EXEC;
    // Note the comma operator because c_str() is only temporary
    queue_opts.socket_path = server_socket_file.c_str(),
    queue_rc = monad_event_queue_connect(
        &queue_opts, &queue, &thread_table, &block_header_table);
    if (queue_rc != 0) {
        errx(
            EX_SOFTWARE,
            "monad_event_queue_connect failed: %s",
            monad_event_queue_get_last_error());
    }

    // Try to open the shared memory segment capture file
    constexpr int output_file_open_flags = O_CREAT | O_RDWR | O_TRUNC;
    constexpr mode_t output_file_open_mode =
        S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;
    int const fd = open(
        output_file.c_str(), output_file_open_flags, output_file_open_mode);
    if (fd == -1) {
        err(EX_OSERR, "unable to open output file `%s`", output_file.c_str());
    }

    // Get the socket peer's credentials so we can signal it to exit and stop
    // writing to the queue after it reaches "last_seqno". The writer process
    // will die but its shared memory segments will still be mapped by us.
    ucred peercred;
    socklen_t peercred_len = sizeof peercred;
    if (getsockopt(
            queue->sock_fd,
            SOL_SOCKET,
            SO_PEERCRED,
            &peercred,
            &peercred_len) == -1) {
        MONAD_ABORT_PRINTF(
            "could not get SO_PEERCRED for server peer: %d", errno);
    }

    // Wait for the writer to write everything, then kill it
    wait_for_seqno(queue, last_seqno, peercred.pid);

    // Dump all the segments to a file
    export_shm_segments(queue, fd, thread_table, block_header_table);
    return 0;
}
