#pragma once

/**
 * @file
 *
 * Defines convenience functions that are useful in most event ring programs,
 * but which are not part of the core API
 */

#include <stddef.h>
#include <stdint.h>

#include <sys/types.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_event_content_type : uint16_t;

/// Arguments for the `monad_event_ring_init_simple` function
struct monad_event_ring_simple_config
{
    uint8_t descriptors_shift;
    uint8_t payload_buf_shift;
    uint16_t context_large_pages;
    enum monad_event_content_type content_type;
    uint8_t const *schema_hash;
};

/// "All in one" convenience event ring file init for simple cases: given an
/// event ring fd and the required options, calculate the required size of the
/// event ring, call fallocate(2) to ensure the storage is available, then call
/// monad_event_ring_init_file
int monad_event_ring_init_simple(
    struct monad_event_ring_simple_config const *, int ring_fd,
    off_t ring_offset, char const *error_name);

/// Check that the event ring content type and schema hash match the assumed
/// values
int monad_event_ring_check_content_type(
    struct monad_event_ring const *, enum monad_event_content_type,
    uint8_t const *schema_hash);

/// Find the pid of every process that has opened the given event ring file
/// descriptor for writing; this is slow, and somewhat brittle (it crawls
/// proc(5) file descriptor tables so depends on your access(2) permissions)
int monad_event_ring_find_writer_pids(int ring_fd, pid_t *pids, size_t *size);

/// Given a path to a file (which does not need to exist), check if the
/// associated file system supports that file being mmap'ed with MAP_HUGETLB
int monad_check_path_supports_map_hugetlb(char const *path, bool *supported);

#ifdef __cplusplus
} // extern "C"
#endif
