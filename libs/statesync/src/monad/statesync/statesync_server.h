#pragma once

#include <monad/statesync/statesync_messages.h>

struct monad_statesync_server;
struct monad_statesync_server_context;
struct monad_statesync_server_network;

struct monad_statesync_server *monad_statesync_server_create(
    struct monad_statesync_server_context *,
    struct monad_statesync_server_network *,
    ssize_t (*statesync_server_recv)(
        struct monad_statesync_server_network *, unsigned char *, size_t),
    void (*statesync_server_send_upsert)(
        struct monad_statesync_server_network *, unsigned char const *key,
        uint64_t key_size, unsigned char const *value, uint64_t value_size,
        bool code),
    void (*statesync_server_send_done)(
        struct monad_statesync_server_network *, struct monad_sync_done));

void monad_statesync_server_run_once(struct monad_statesync_server *);

void monad_statesync_server_destroy(struct monad_statesync_server *);
