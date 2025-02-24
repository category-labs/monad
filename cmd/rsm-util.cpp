/**
 * @file
 *
 * This command line utility can dump a snapshot of all the execution event
 * shared memory segments to a single file, or read a snapshot produced by
 * this utility. This is used to persist static input data for test cases.
 */

#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <string>
#include <utility>

#include <err.h>
#include <fcntl.h>
#include <signal.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sysexits.h>
#include <unistd.h>

#include <CLI/CLI.hpp>
#include <zstd.h>

#include <monad/core/assert.h>
#include <monad/core/bit_util.h>
#include <monad/event/event.h>
#include <monad/event/event_iterator.h>
#include <monad/event/event_ring_db.h>
#include <monad/event/event_test_util.h>

// TODO(ken): supposed to come from mem/align.h but the PR hasn't landed yet
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t size, size_t align)
{
    MONAD_DEBUG_ASSERT(std::has_single_bit(align));
    return bit_round_up(size, static_cast<unsigned>(std::countr_zero(align)));
}

static void wait_for_seqno(
    monad_event_ring_db const *ring_db, monad_event_ring *event_ring,
    uint64_t last_seqno)
{
    std::fprintf(
        stderr,
        "waiting for pid %d to materialize seqno: %lu\n",
        ring_db->exec_pid,
        last_seqno);

    monad_event_iterator iter;
    monad_event_iterator_init(&iter, event_ring);

    // Manually rewind to the beginning
    iter.read_last_seqno = 0;
    while (true) {
        monad_event_descriptor event;
        switch (monad_event_iterator_try_next(&iter, &event)) {
        case MONAD_EVENT_GAP:
            MONAD_ABORT("unexpected gap during last_seqno wait");

        case MONAD_EVENT_PAYLOAD_EXPIRED:
            std::unreachable(); // Never actually returned by try_next

        case MONAD_EVENT_NOT_READY:
            continue;

        case MONAD_EVENT_SUCCESS:
            if (event.seqno >= last_seqno) {
                syscall(
                    SYS_pidfd_send_signal, ring_db->pidfd, SIGINT, nullptr, 0);
                fprintf(
                    stderr,
                    "saw seqno: %lu, sent signal %d to pid %d\n",
                    event.seqno,
                    SIGINT,
                    ring_db->exec_pid);
                return;
            }
            break;
        }
    }
}

void snapshot_event_ring(
    monad_event_ring_db const *ring_db, monad_event_ring const *event_ring,
    std::FILE *out)
{
    monad_event_ring_db_data snapshot_db;
    size_t const mmap_page_size = static_cast<size_t>(getpagesize());

    // Create a ring db that is a copy of the one from the terminated process,
    // and clear all the db entries for all rings except MONAD_EVENT_RING_EXEC
    memcpy(&snapshot_db, ring_db->db_data, sizeof *ring_db->db_data);
    snapshot_db.is_snapshot = true;
    for (monad_event_ring_db_entry &e : snapshot_db.rings) {
        if (e.ring_type != MONAD_EVENT_RING_EXEC) {
            e.ring_control.ring_state = MONAD_EVENT_RING_OFFLINE;
            memset(
                &e.ring_capacity,
                0,
                sizeof e - offsetof(monad_event_ring_db_entry, ring_capacity));
        }
    }

    // For the execution ring, set the file offsets to where they should
    // be if we copy each ring object into the stream. We have to align the
    // first object to a page boundary so that it's offset will be suitably
    // aligned to be mmap'ed later.
    monad_event_ring_db_entry &db_entry =
        snapshot_db.rings[MONAD_EVENT_RING_EXEC];
    size_t const ring_offset =
        monad_round_size_to_align(sizeof snapshot_db, mmap_page_size);
    db_entry.ring_data_offset = static_cast<off_t>(ring_offset);
    size_t const ring_size =
        db_entry.ring_capacity * sizeof(monad_event_descriptor) +
        db_entry.payload_buf_size;
    size_t const snapshot_size = ring_offset + ring_size;

    std::fprintf(stderr, "copying %lu bytes to snapshot buffer\n", ring_size);
    std::unique_ptr<std::byte[]> const snapshot_buf{
        new std::byte[snapshot_size]};
    memcpy(snapshot_buf.get(), &snapshot_db, sizeof snapshot_db);
    void *next = snapshot_buf.get() + ring_offset;
    next = mempcpy(
        next,
        event_ring->descriptors,
        event_ring->capacity * sizeof(monad_event_descriptor));
    mempcpy(next, event_ring->payload_buf, event_ring->payload_buf_size);

    std::fprintf(stderr, "compressing %lu bytes...", snapshot_size);
    size_t const compress_buf_len = ZSTD_compressBound(snapshot_size);
    std::unique_ptr<std::byte[]> const compress_buf{
        new std::byte[compress_buf_len]};
    size_t const compressed_len = ZSTD_compress(
        compress_buf.get(),
        compress_buf_len,
        snapshot_buf.get(),
        snapshot_size,
        ZSTD_maxCLevel());
    MONAD_ASSERT(ZSTD_isError(compressed_len) == 0);
    std::fprintf(stderr, "compressed to %lu bytes\n", compressed_len);

    // Write the ZSTD magic indicator, the full uncompressed size, move the
    // file to a page boundary so it can be mmaped.
    monad_event_rsm_header rsm_header = {
        .decompressed_size = snapshot_size,
        .ring_capacity = db_entry.ring_capacity,
        .ring_offset = ring_offset};
    memcpy(
        &rsm_header.magic, MONAD_EVENT_RSM_MAGIC, sizeof MONAD_EVENT_RSM_MAGIC);
    size_t n_items = fwrite(&rsm_header, sizeof rsm_header, 1, out);
    MONAD_ASSERT(n_items == 1);
    n_items = fwrite(compress_buf.get(), compressed_len, 1, out);
    MONAD_ASSERT(n_items == 1);
}

static void snapshot_main(std::string const &shm_name, uint64_t last_seqno)
{
    if (isatty(STDOUT_FILENO)) {
        errx(EX_USAGE, "stdout is a terminal device; `snap` cannot write");
    }

    // Connect to the execution process
    monad_event_ring_db ring_db;
    if (monad_event_ring_db_open(&ring_db, shm_name.c_str()) != 0) {
        errx(
            EX_SOFTWARE,
            "event library error -- %s",
            monad_event_ring_db_get_last_error());
    }

    // Import the execution ring
    monad_event_ring event_ring;
    if (monad_event_ring_db_import(
            &ring_db, MONAD_EVENT_RING_EXEC, &event_ring) != 0) {
        errx(
            EX_SOFTWARE,
            "event library error -- %s",
            monad_event_ring_db_get_last_error());
    }

    // Wait for the writer to write up to `last_seqno`, then kill with SIGINT
    wait_for_seqno(&ring_db, &event_ring, last_seqno);

    // Dump the execution event ring to a compressed file
    snapshot_event_ring(&ring_db, &event_ring, stdout);
}

static void load_main(std::string const &shm_name)
{
    if (isatty(STDIN_FILENO)) {
        errx(EX_USAGE, "stdin is a terminal device; `load` cannot read");
    }
    if (monad_event_rsm_load_snapshot_from_fd(
            STDIN_FILENO, "stdin", shm_name.c_str()) != 0) {
        errx(
            EX_SOFTWARE,
            "event library error -- %s",
            monad_event_rsm_get_last_error());
    }
}

int main(int argc, char **argv)
{
    std::string shm_name = MONAD_EVENT_DEFAULT_RING_DB_SHM_NAME;
    uint64_t last_seqno;

    CLI::App cli{"event ring shared memory tool"};

    CLI::App *snap_command = cli.add_subcommand(
        "snap", "write a snapshot of the execution event ring to stdout");
    snap_command
        ->add_option(
            "-s,--shm-name", shm_name, "shm_open name for event ring db")
        ->capture_default_str();
    snap_command
        ->add_option(
            "last",
            last_seqno,
            "(approximate) last sequence number to place in the file")
        ->required();
    snap_command->final_callback(
        [&shm_name, &last_seqno] { snapshot_main(shm_name, last_seqno); });

    CLI::App *load_command =
        cli.add_subcommand("load", "load a snapshot file from stdin");
    load_command
        ->add_option(
            "shm_name",
            shm_name,
            "shared memory object where ring db will be loaded")
        ->required();
    load_command->final_callback([&shm_name] { load_main(shm_name); });

    cli.require_subcommand(1, 1);
    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(cli.exit(e));
    }
    catch (CLI::ParseError const &e) {
        std::exit(cli.exit(e));
    }

    return 0;
}
