#pragma once

/**
 * @file
 *
 * This file defines an API to programtically create a "snapshot" ring db from
 * an RSM snapshot file, see event_recorder.md for details
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

int monad_event_rsm_load_snapshot_from_bytes(
    void const *rsm_bytes, size_t rsm_len, char const *error_name,
    char const *shm_name);

int monad_event_rsm_load_snapshot_from_fd(
    int fd, char const *error_name, char const *shm_name);

int monad_event_rsm_load_snapshot_from_file(
    char const *path, char const *shm_name);

char const *monad_event_rsm_get_last_error();

static uint8_t const MONAD_EVENT_RSM_MAGIC[] = {
    'R', 'I', 'N', 'G', 'S', 'N', 'A', 'P'};

struct monad_event_rsm_header
{
    uint8_t magic[sizeof MONAD_EVENT_RSM_MAGIC];
    size_t decompressed_size;
    size_t ring_capacity;
    size_t ring_offset;
};

#ifdef __cplusplus
} // extern "C"
#endif
