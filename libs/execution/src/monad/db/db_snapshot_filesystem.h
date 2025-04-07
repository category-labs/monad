#pragma once

#include <monad/db/db_snapshot.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_db_snapshot_filesystem_write_user_context;

struct monad_db_snapshot_filesystem_write_user_context *
monad_db_snapshot_filesystem_write_user_context_create(
    char const *root, uint64_t block);

void monad_db_snapshot_filesystem_write_user_context_destroy(
    struct monad_db_snapshot_filesystem_write_user_context *);

uint64_t monad_db_snapshot_write_filesystem(
    uint64_t shard, monad_snapshot_type, unsigned char const *bytes, size_t len,
    void *user);

void monad_db_snapshot_load_filesystem(
    char const *const *dbname_paths, size_t len, unsigned sq_thread_cpu,
    char const *snapshot_dir, uint64_t block);

#ifdef __cplusplus
}
#endif
