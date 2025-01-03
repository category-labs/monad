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
#include <sys/mman.h>
#include <sys/socket.h>
#include <sysexits.h>
#include <unistd.h>

#include <CLI/CLI.hpp>
#include <zlib.h>

#include <monad/core/assert.h>
#include <monad/core/bit_util.h>
#include <monad/event/event.h>
#include <monad/event/event_client.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>

namespace fs = std::filesystem;

constexpr size_t PAGE_2MB = 1UL << 21;

struct test_file_writer
{
    int fd;
    size_t segments_written;
    Bytef *compress_buf;
    uLongf compress_buf_len;
};

// A test file is an array of these entries (terminated by an all-zero
// sentinel) explaining where the various other segments in the file are
// written and what they contain
struct test_file_segment
{
    uint16_t type;
    uint64_t compressed_len;
    uint64_t segment_len;
    uint64_t offset;

    union
    {
        uint16_t metadata_type;
        size_t ring_capacity;
    };
};

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
static size_t monad_round_size_to_align(size_t size, size_t align)
{
    MONAD_DEBUG_ASSERT(std::has_single_bit(align));
    return bit_round_up(size, static_cast<unsigned>(std::countr_zero(align)));
}

static void
init_test_file_writer(test_file_writer *tfw, int fd, size_t max_size)
{
    tfw->fd = fd;
    tfw->segments_written = 0;
    // Skip over the first page, which will hold the segment directory.
    off_t const skip = static_cast<off_t>(getpagesize());
    off_t o = ftruncate(tfw->fd, skip);
    MONAD_ASSERT(o != -1);
    o = lseek(tfw->fd, skip, SEEK_SET);
    MONAD_ASSERT(o != -1);

    // Allocate a buffer to hold the compressed data (given to zlib for
    // compress2 output)
    tfw->compress_buf_len = static_cast<uLongf>(
        monad_round_size_to_align(compressBound(max_size), PAGE_2MB));
    tfw->compress_buf = static_cast<Bytef *>(mmap(
        nullptr,
        tfw->compress_buf_len,
        PROT_READ | PROT_WRITE,
        MAP_ANONYMOUS | MAP_PRIVATE | MAP_HUGETLB,
        -1,
        0));
    MONAD_ASSERT(tfw->compress_buf != MAP_FAILED);
}

static void save_mmap_region(
    test_file_writer *tfw, test_file_segment *segment, void const *data,
    size_t length)
{
    // Compress the memory segment
    uLongf compressed_len = tfw->compress_buf_len;
    int const z_result = compress2(
        tfw->compress_buf,
        &compressed_len,
        static_cast<Bytef const *>(data),
        static_cast<uLongf>(length),
        Z_BEST_COMPRESSION);
    MONAD_ASSERT(z_result == Z_OK);

    // Write the segment descriptor describing the memory segment we're dumping
    segment->segment_len = length;
    segment->compressed_len = static_cast<uint64_t>(compressed_len);
    off_t curoff = lseek(tfw->fd, 0, SEEK_CUR);
    MONAD_ASSERT(curoff != -1);
    segment->offset = (uint64_t)curoff;
    ssize_t wr_bytes = pwrite(
        tfw->fd,
        segment,
        sizeof *segment,
        static_cast<off_t>(sizeof(*segment) * tfw->segments_written++));
    MONAD_ASSERT(wr_bytes == sizeof(*segment));

    // Write the compressed segment data
    wr_bytes = write(tfw->fd, tfw->compress_buf, segment->compressed_len);
    MONAD_ASSERT(wr_bytes == static_cast<ssize_t>(segment->compressed_len));
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
    munmap(tfw->compress_buf, static_cast<size_t>(tfw->compress_buf_len));
}

static void wait_for_seqno(
    monad_event_imported_ring *import, uint64_t last_seqno, pid_t pid)
{
    std::fprintf(
        stdout,
        "waiting for pid %d to materialize seqno: %lu\n",
        pid,
        last_seqno);

    monad_event_iterator iter;
    monad_event_imported_ring_init_iter(import, &iter);

    // Manually rewind to the beginning
    iter.last_seqno = 0;
    while (true) {
        monad_event_descriptor const *event;
        switch (monad_event_iterator_peek(&iter, &event)) {
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
            monad_event_iterator_advance(&iter);
            break;
        }
    }
}

void export_shm_segments(monad_event_imported_ring *import, int fd)
{
    test_file_writer tfw{};
    test_file_segment segment{};

    // Setup the output structure and skip over the fixed-size segment
    // descriptor table
    init_test_file_writer(&tfw, fd, import->ring.payload_buf_size);

    // Write the control page
    segment.type = MONAD_EVENT_MSG_MAP_RING_CONTROL;
    segment.ring_capacity = import->ring.capacity;
    save_mmap_region(
        &tfw,
        &segment,
        import->ring.control,
        static_cast<size_t>(getpagesize()));

    // Write the descriptor table
    segment.type = MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE;
    save_mmap_region(
        &tfw,
        &segment,
        import->ring.descriptor_table,
        sizeof(struct monad_event_descriptor) * import->ring.capacity);

    // Write the payload buffer
    segment.type = MONAD_EVENT_MSG_MAP_PAYLOAD_BUFFER;
    save_mmap_region(
        &tfw,
        &segment,
        import->ring.payload_buf,
        import->ring.payload_buf_size);

    // Write the metadata page
    segment.type = MONAD_EVENT_MSG_MAP_METADATA_PAGE;
    monad_event_proc *const proc = import->proc;
    save_mmap_region(
        &tfw, &segment, proc->metadata_page, proc->metadata_page_len);

    // Export thread table and block table offset; we manually write these
    // metadata sections since there is no associated mmap region for them
    ssize_t wr_bytes;
    segment.type = MONAD_EVENT_MSG_METADATA_OFFSET;
    segment.segment_len = segment.compressed_len = 0;

    segment.metadata_type = MONAD_EVENT_METADATA_THREAD;
    auto const *thread_table_u8 =
        std::bit_cast<uint8_t const *>(proc->thread_table);
    segment.offset = static_cast<uint64_t>(
        thread_table_u8 - std::bit_cast<uint8_t const *>(proc->metadata_page));
    wr_bytes = pwrite(
        tfw.fd,
        &segment,
        sizeof(segment),
        static_cast<off_t>(sizeof(segment) * tfw.segments_written++));
    MONAD_ASSERT(wr_bytes == sizeof(segment));

    segment.metadata_type = MONAD_EVENT_METADATA_BLOCK_FLOW;
    auto const *block_header_table_u8 =
        std::bit_cast<uint8_t const *>(proc->block_header_table);
    segment.offset = static_cast<uint64_t>(
        block_header_table_u8 -
        std::bit_cast<uint8_t const *>(proc->metadata_page));
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
    monad_event_connect_options connect_opts{};

    // Defaults
    connect_opts.socket_timeout.tv_sec = 1;

    CLI::App cli{"monad event export shared memory tool"};
    cli.add_option(
           "-s,--server", server_socket_file, "path to the server socket file")
        ->capture_default_str();
    cli.add_option(
           "--timeout",
           connect_opts.socket_timeout.tv_sec,
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

    // Connect to the execution process
    int connect_rc;
    monad_event_proc *exec_proc;
    // Note the comma operator because c_str() is only temporary
    connect_opts.socket_path = server_socket_file.c_str(),
    connect_rc = monad_event_proc_connect(&connect_opts, &exec_proc);
    if (connect_rc != 0) {
        errx(
            EX_SOFTWARE,
            "monad_event_proc_connect failed: %s",
            monad_event_proc_get_last_error());
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
    // writing to the ring after it reaches "last_seqno". The writer process
    // will die but its shared memory segments will still be mapped by us.
    ucred peercred;
    socklen_t peercred_len = sizeof peercred;
    if (getsockopt(
            exec_proc->sock_fd,
            SOL_SOCKET,
            SO_PEERCRED,
            &peercred,
            &peercred_len) == -1) {
        MONAD_ABORT_PRINTF(
            "could not get SO_PEERCRED for server peer: %d", errno);
    }

    monad_event_imported_ring *import;
    if (monad_event_proc_import_ring(
            exec_proc, MONAD_EVENT_RING_EXEC, &import) != 0) {
        errx(
            EX_SOFTWARE,
            "monad_event_proc_import_ring failed: %s",
            monad_event_proc_get_last_error());
    }

    // Wait for the writer to write everything, then kill it
    wait_for_seqno(import, last_seqno, peercred.pid);

    // Dump all the segments to a file
    export_shm_segments(import, fd);
    return 0;
}
