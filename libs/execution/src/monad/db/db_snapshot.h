#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

struct monad_db_snapshot_loader;

enum monad_snapshot_type
{
    MONAD_SNAPSHOT_ETH_HEADER = 0,
    MONAD_SNAPSHOT_ACCOUNT,
    MONAD_SNAPSHOT_STORAGE,
    MONAD_SNAPSHOT_CODE
};

bool monad_db_dump_snapshot(
    char const *const *dbname_paths, size_t len, unsigned sq_thread_cpu,
    uint64_t block,
    uint64_t (*write)(
        uint64_t shard, enum monad_snapshot_type, unsigned char const *bytes,
        size_t len, void *user),
    void *user);

struct monad_db_snapshot_loader *monad_db_snapshot_loader_create(
    uint64_t block, char const *const *dbname_paths, size_t len,
    unsigned sq_thread_cpu);

void monad_db_snapshot_loader_load(
    struct monad_db_snapshot_loader *loader, uint64_t shard,
    unsigned char const *eth_header, size_t, unsigned char const *account,
    size_t, unsigned char const *storage, size_t, unsigned char const *code,
    size_t);

void monad_db_snapshot_loader_destroy(struct monad_db_snapshot_loader *);

#ifdef __cplusplus
}
#endif
