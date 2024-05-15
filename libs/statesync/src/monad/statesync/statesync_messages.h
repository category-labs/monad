#pragma once

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_sync_type : uint8_t
{
    SyncTypeRequest = 0,
    SyncTypeTarget = 1,
    SyncTypeUpsertHeader = 2,
    SyncTypeDone = 3,
};

static_assert(sizeof(enum monad_sync_type) == 1);
static_assert(alignof(enum monad_sync_type) == 1);

struct monad_sync_request
{
    uint64_t prefix;
    uint8_t prefix_bytes;
    uint64_t target;
    uint64_t from;
    uint64_t until;
    uint64_t old_target;
};

static_assert(sizeof(struct monad_sync_request) == 48);
static_assert(alignof(struct monad_sync_request) == 8);

struct monad_sync_target
{
    uint64_t n;
    unsigned char state_root[32];
};

static_assert(sizeof(struct monad_sync_target) == 40);
static_assert(alignof(struct monad_sync_target) == 8);

struct monad_sync_upsert_header
{
    bool code;
    uint64_t key_size;
    uint64_t value_size;
};

static_assert(sizeof(struct monad_sync_upsert_header) == 24);
static_assert(alignof(struct monad_sync_upsert_header) == 8);

struct monad_sync_done
{
    bool success;
    uint64_t prefix;
    uint64_t n;
};

static_assert(sizeof(struct monad_sync_done) == 24);
static_assert(alignof(struct monad_sync_done) == 8);

#ifdef __cplusplus
}
#endif
