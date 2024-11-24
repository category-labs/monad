#pragma once

/**
 * @file
 *
 * API for connecting to an event queue from an external process and exporting
 * its shared memory segments
 */

#include <stddef.h>
#include <stdint.h>

#include <sys/time.h>

enum monad_event_queue_type : uint8_t;

#ifdef __cplusplus
extern "C"
{
#endif

/// Configuration options needed to connect to an event queue
struct monad_event_queue_options
{
    char const *socket_path; ///< Path to event server's UNIX domain socket
    struct timeval socket_timeout; ///< recvmsg(2) ETIMEDOUT if silent this long
    enum monad_event_queue_type queue_type; ///< What kind of events we want
};

struct monad_event_queue;
struct monad_event_queue_ffi_extra;
struct monad_event_reader;

struct monad_event_block_exec_header;
struct monad_event_thread_info;

/// Connect to an event queue with the provided options
int monad_event_queue_connect(
    struct monad_event_queue_options const *, struct monad_event_queue **,
    struct monad_event_thread_info const **,
    struct monad_event_block_exec_header const **);

/// Disconnect from an event queue previously connected to with
/// monad_event_queue_connect; this cleans up the shared memory resources
/// exported into our process from the event producer process
void monad_event_queue_disconnect(struct monad_event_queue *);

/// Test whether the event server is still connected; this is an expensive
/// function (it requires a system call on the socket), so high performance
/// clients should not call this in a tight event polling loop
bool monad_event_queue_is_connected(struct monad_event_queue const *);

/// Initialize a reader of the queue; each reader has its own state, and this
/// is called once to initialize that state at set the initial iteration point;
/// afterwards, monad_event_reader_reset can be used to reseat the iterator
uint64_t monad_event_queue_init_reader(
    struct monad_event_queue const *, struct monad_event_reader *,
    struct monad_event_queue_ffi_extra *);

/// Get details about the last error that occurred on this thread
char const *monad_event_queue_get_last_error();

/// Structure which is used in the event queue FFI bindings in other languages
/// that have bounds-checked arrays or slices (e.g., Rust)
struct monad_event_queue_ffi_extra
{
    size_t desc_table_size; ///< Full size of descriptor table, including wrap
    uint16_t num_payload_pages; ///< Total number of exported payload pages
};

#ifdef __cplusplus
} // extern "C"
#endif
