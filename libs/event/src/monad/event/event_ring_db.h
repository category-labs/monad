#pragma once

/**
 * @file
 *
 * Defines the "ring db" shared memory structure that describes which event
 * rings are available in a running execution daemon, and how to load them.
 */

#include <stddef.h>
#include <stdint.h>

#include <sys/types.h>

#include <monad/event/event.h>
#include <monad/event/event_types.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// This structure represents an opened "ring database" (ring db); a ring db is
/// a simple file that describes where in shared memory the event rings are
/// located, along with some other metadata used by the event system.
///
/// The actual contents of the ring db are mmap'ed as the `db_data` field;
/// the other fields in this structure are used for performing tasks like
/// checking if the associated execution daemon (the owner of shared memory
/// object) is still alive.
struct monad_event_ring_db
{
    pid_t exec_pid; ///< pid of execution daemon owning the db
    int pidfd; ///< Linux pidfd for `exec_pid` process
    int db_fd; ///< File that db_data is mmap'ed from
    struct monad_event_ring_db_data *db_data; ///< Contents of the ring db
};

// clang-format off

/// Describes which event ring an event is recorded to; an execution process
/// contains a fixed number of event rings, and different categories of events
/// are recorded to different rings
enum monad_event_ring_type : uint8_t
{
    MONAD_EVENT_RING_EXEC,  ///< Core execution events
    MONAD_EVENT_RING_TRACE, ///< Performance tracing events
    MONAD_EVENT_RING_COUNT, ///< Number of recognized ring types
};

/// An entry describing an event ring in the ring db
struct monad_event_ring_db_entry
{
    enum monad_event_ring_type
        ring_type;               ///< Event ring we're describing
    char ring_name[15];          ///< Human-readable name of the ring
    size_t ring_capacity;        ///< # entries in event descriptor array
    size_t payload_buf_size;     ///< Byte size of payload buffer
    size_t payload_buf_map_size; ///< Actual mapped buffer size (w/ wrap-around)
    int ring_data_fd;            ///< File descriptor to actual ring contents
    off_t ring_data_offset;      ///< mmap offset in ring_data_fd to ring data
    struct monad_event_ring_control
        ring_control;            ///< Event ring's state
};

/// The content of a ring db file is a single instance of this structure
struct monad_event_ring_db_data
{
    char magic[7];                     ///< "RING_DB" literal
    bool is_snapshot;                  ///< True -> snapshot from an RSM file
    unsigned db_version;               ///< ABI version of db structures
    uint8_t metadata_hash[32];         ///< Checks that event_types.h matches
    struct monad_event_ring_db_entry
        rings[MONAD_EVENT_RING_COUNT]; ///< Status of all event rings in proc
    struct monad_event_thread_info
        thread_info[256];              ///< Execution daemon thread metadata
    struct monad_event_block_exec_header
        block_headers[4096];           ///< Metadata for active block headers
};

// clang-format on

/// Open a ring db with the given POSIX shared memory name
int monad_event_ring_db_open(
    struct monad_event_ring_db *, char const *shm_name);

/// Release the ring db resources
void monad_event_ring_db_close(struct monad_event_ring_db *);

/// Return true if the execution daemon associated with the ring db is still
/// running
bool monad_event_ring_db_is_alive(struct monad_event_ring_db const *);

/// Import an event ring into our process' address space, using the information
/// in the given ring db
int monad_event_ring_db_import(
    struct monad_event_ring_db const *, enum monad_event_ring_type,
    struct monad_event_ring *);

/// Get details about the last error that occurred on this thread
char const *monad_event_ring_db_get_last_error();

#define MONAD_EVENT_DEFAULT_RING_DB_SHM_NAME "/monad_event_ring_db"
#define MONAD_EVENT_RING_DB_VERSION 1U

static const uint8_t MONAD_EVENT_RING_DB_MAGIC[] = {
    'R', 'I', 'N', 'G', '_', 'D', 'B'};

#ifdef __cplusplus
} // extern "C"
#endif
