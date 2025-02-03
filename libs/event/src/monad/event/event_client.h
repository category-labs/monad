#pragma once

/**
 * @file
 *
 * API for connecting to an execution daemon and importing its event rings
 */

#include <stdatomic.h>
#include <stdint.h>

#include <pthread.h>
#include <sys/queue.h>
#include <sys/time.h>

#include <monad/event/event.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Options needed to connect to the execution process
struct monad_event_connect_options
{
    char const *socket_path; ///< Path to event server's UNIX domain socket
    struct timeval socket_timeout; ///< recvmsg(2) ETIMEDOUT if silent this long
};

struct monad_event_imported_ring;
struct monad_event_iterator;
struct monad_event_proc;

/// Connect to an execution process with the provided options
int monad_event_proc_connect(
    struct monad_event_connect_options const *, struct monad_event_proc **);

/// Disconnect from the execution process previously connected to with
/// monad_event_proc_connect; it is still safe to use any imported event rings
/// after disconnecting, but this pointer cannot be safely dereferenced
/// afterward
int monad_event_proc_disconnect(struct monad_event_proc *);

/// Test whether the event server is still connected; this is an expensive
/// function (it requires a system call on the socket), so high performance
/// clients should not call this in a tight event polling loop
bool monad_event_proc_is_connected(struct monad_event_proc const *);

/// Import an event ring into this process
int monad_event_proc_import_ring(
    struct monad_event_proc *, enum monad_event_ring_type,
    struct monad_event_imported_ring **);

/// Increment the reference count on an imported event ring
struct monad_event_imported_ring *
monad_event_imported_ring_acquire(struct monad_event_imported_ring *);

/// Decrement the reference count on an imported event ring
bool monad_event_imported_ring_release(struct monad_event_imported_ring *);

/// Initialize an iterator to an event ring; each iterator has its own state,
/// and this is called once to initialize that state and set the initial
/// iteration point
int monad_event_imported_ring_init_iter(
    struct monad_event_imported_ring const *, struct monad_event_iterator *);

/// Get details about the last error that occurred on this thread
char const *monad_event_proc_get_last_error();

/// Maximum number of simultaneous monad_event_proc objects that can be in use
/// at one time
#define MONAD_EVENT_PROC_MAX (32)

/// Maximum number of simultaneous monad_event_imported_ring objects that can
/// be in use at one time
#define MONAD_EVENT_IMPORTED_RING_MAX (32)

struct monad_event_block_exec_header;
struct monad_event_thread_info;

struct monad_event_proc
{
    atomic_uint refcount;
    int sock_fd;
    struct monad_event_thread_info const *thread_table;
    struct monad_event_block_exec_header const *block_header_table;
    void const *metadata_page;
    size_t metadata_page_len;
    pthread_mutex_t mtx;
    TAILQ_HEAD(, monad_event_imported_ring) imports;
};

// clang-format off

struct monad_event_imported_ring
{
    atomic_uint refcount;                ///< Reference count keeping us alive
    enum monad_event_ring_type type;     ///< What kind of ring this is
    struct monad_event_ring ring;        ///< Mapping of ring in our addr space
    size_t true_payload_buf_size;        ///< Buffer size + overwrite (for Rust)
    struct monad_event_proc *proc;       ///< Process that exported us
    TAILQ_ENTRY(monad_event_imported_ring) next; ///< Link for all proc imports
};

// clang-format on

#ifdef __cplusplus
} // extern "C"
#endif
