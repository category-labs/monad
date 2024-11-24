#pragma once

/**
 * @file
 *
 * Declarations shared between various event server implementation files
 */

struct monad_event_client;
struct monad_event_open_queue_msg;
struct monad_event_server;
struct monad_event_server_options;

// Sends an OPEN_ERROR message to the client explaining why the server could
// not open the queue, then call closes the client
__attribute__((format(printf, 3, 4))) typedef void(close_client_err_fn)(
    struct monad_event_client *client, int error, char const *format, ...);

struct shared_mem_export_ops
{
    void (*cleanup)(void *opaque);

    bool (*export)(
        struct monad_event_open_queue_msg const *open_msg, int sock_fd,
        unsigned client_id, close_client_err_fn *close_fn,
        struct monad_event_client *client, void *opaque, unsigned *nmsgs);

    void (*heartbeat)(void *opaque);
};

int _monad_event_server_create_common(
    struct monad_event_server_options const *,
    struct shared_mem_export_ops const *, void *export_state,
    struct monad_event_server **);
