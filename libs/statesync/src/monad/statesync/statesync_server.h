#pragma once

#include <monad/statesync/statesync_messages.h>

struct monad_statesync_server;
struct monad_statesync_server_context;
struct monad_statesync_server_network;

struct monad_statesync_server *monad_statesync_server_create(
    monad_statesync_server_context *const ctx,
    monad_statesync_server_network *const net,
    monad_sync_request (*statesync_server_recv)(
        monad_statesync_server_network *),
    void (*statesync_server_send_upsert)(
        monad_statesync_server_network *, monad_sync_type,
        unsigned char const *v1, uint64_t size1, unsigned char const *v2,
        uint64_t size2),
    void (*statesync_server_send_done)(
        monad_statesync_server_network *, struct monad_sync_done));

void monad_statesync_server_run_once(struct monad_statesync_server *);

void monad_statesync_server_destroy(struct monad_statesync_server *);
