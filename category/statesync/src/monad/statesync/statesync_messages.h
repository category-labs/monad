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
    SYNC_TYPE_REQUEST = 0,
    SYNC_TYPE_TARGET = 1,
    SYNC_TYPE_DONE = 2,
    SYNC_TYPE_UPSERT_CODE = 3,
    SYNC_TYPE_UPSERT_ACCOUNT = 4,
    SYNC_TYPE_UPSERT_STORAGE = 5,
    SYNC_TYPE_UPSERT_ACCOUNT_DELETE = 6,
    SYNC_TYPE_UPSERT_STORAGE_DELETE = 7,
    SYNC_TYPE_UPSERT_HEADER = 8,
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
