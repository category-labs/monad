#pragma once

#include <monad/statesync/statesync_messages.h>

#ifdef __cplusplus
extern "C"
{
#endif

extern unsigned const MONAD_SQPOLL_DISABLED;

struct monad_statesync_client;
struct monad_statesync_client_context;

struct monad_statesync_client_context *monad_statesync_client_context_create(
    char const *const *dbname_paths, size_t len, char const *genesis_file,
    unsigned sq_thread_cpu, struct monad_statesync_client *,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request));

uint8_t monad_statesync_client_prefix_len();

size_t monad_statesync_client_prefixes();

bool monad_statesync_client_has_reached_target(
    struct monad_statesync_client_context const *);

void monad_statesync_client_handle_new_peer(
    struct monad_statesync_client_context *, uint64_t prefix, uint32_t version);

void monad_statesync_client_handle_target(
    struct monad_statesync_client_context *, unsigned char const *, uint64_t);

bool monad_statesync_client_handle_upsert(
    struct monad_statesync_client_context *, uint64_t prefix,
    enum monad_sync_type, unsigned char const *, uint64_t);

void monad_statesync_client_handle_done(
    struct monad_statesync_client_context *, struct monad_sync_done);

bool monad_statesync_client_finalize(struct monad_statesync_client_context *);

void monad_statesync_client_context_destroy(
    struct monad_statesync_client_context *);

#ifdef __cplusplus
}
#endif
