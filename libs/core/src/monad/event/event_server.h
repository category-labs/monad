#pragma once

/**
 * @file
 *
 * This file defines the event server interface, which can be used to host
 * an event server within a process. A server allows the caller to export an
 * event ring's shared memory segments to external applications over a UNIX
 * domain socket.
 *
 * There is no synchronization in the server: it is expected that only a single
 * thread at a time will call server functions.
 */

#include <signal.h>

struct timespec;

#ifdef __cplusplus
extern "C"
{
#endif

typedef void(monad_event_server_log_fn)(int severity, char const *msg, void *);

/// Configuration options passed to the server creation function
struct monad_event_server_options
{
    monad_event_server_log_fn *log_fn; ///< Callback for all server logging
    void *log_context; ///< Context object passed into log_fn
    char const *socket_path; ///< Address of the UNIX domain socket
};

struct monad_event_server;

/// Create an event server with the given options
int monad_event_server_create(
    struct monad_event_server_options const *, struct monad_event_server **);

/// Destroy an event server
void monad_event_server_destroy(struct monad_event_server *);

/// Return true if calling monad_event_server_process_work will perform an
/// action without waiting
bool monad_event_server_has_pending_work(struct monad_event_server *);

/// Wait for socket messages to arrive (for up to `timeout` time) and handle
/// any requests that come from clients; it may publish the HEARTBEAT event.
/// This is effectively a single iteration of the "main loop" of the event
/// server, and should be called on a separate (low priority) thread
int monad_event_server_process_work(
    struct monad_event_server *, struct timespec const *timeout,
    sigset_t const *sigmask, unsigned *rings_exported);

#ifdef __cplusplus
} // extern "C"
#endif
