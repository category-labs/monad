#pragma once

/**
 * @file
 *
 * Definition of the event ring shared memory export interface. This allows
 * different implementations of the export operation, e.g., the real event
 * server (which exports event recorder rings) vs. the fake event server,
 * which exports snapshots of shared memory produced by the `snapshot-rsm`
 * utility
 */

struct monad_event_client;
struct monad_event_server;
struct monad_event_server_options;

// Functions of this type send an EXPORT_ERROR message to the client
// explaining why the server could not export event the ring, and then close
// the client's connection
__attribute__((format(printf, 3, 4))) typedef void(close_client_err_fn)(
    struct monad_event_client *client, int error, char const *format, ...);

// Shared memory export interface
struct shared_mem_export_ops
{
    void (*cleanup)(void *opaque);

    bool (*export_metadata)(
        int sock_fd, unsigned client_id, close_client_err_fn *close_fn,
        struct monad_event_client *client, void *opaque, unsigned *nmsgs);

    bool (*export_ring)(
        enum monad_event_ring_type, uint8_t const (*event_metadata_hash)[32],
        int sock_fd, unsigned client_id, close_client_err_fn *close_fn,
        struct monad_event_client *client, void *opaque, unsigned *nmsgs);

    void (*send_heartbeat)(void *opaque);
};

int _monad_event_server_create_common(
    struct monad_event_server_options const *,
    struct shared_mem_export_ops const *, void *export_state,
    struct monad_event_server **);
