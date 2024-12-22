#pragma once

/**
 * @file
 *
 * Declarations shared between various event server implementation files
 */

struct monad_event_client;
struct monad_event_import_ring_msg;
struct monad_event_server;
struct monad_event_server_options;

// Sends an EXPORT_ERROR message to the client explaining why the server could
// not export the ring, then closes the client
__attribute__((format(printf, 3, 4))) typedef void(close_client_err_fn)(
    struct monad_event_client *client, int error, char const *format, ...);

struct shared_mem_export_ops
{
    void (*cleanup)(void *opaque);

    bool (*export_metadata)(
        int sock_fd, unsigned client_id, close_client_err_fn *close_fn,
        struct monad_event_client *client, void *opaque, unsigned *nmsgs);

    bool (*export_ring)(
        struct monad_event_export_ring_msg const *export_msg, int sock_fd,
        unsigned client_id, close_client_err_fn *close_fn,
        struct monad_event_client *client, void *opaque, unsigned *nmsgs);

    void (*heartbeat)(void *opaque);
};

int _monad_event_server_create_common(
    struct monad_event_server_options const *,
    struct shared_mem_export_ops const *, void *export_state,
    struct monad_event_server **);
