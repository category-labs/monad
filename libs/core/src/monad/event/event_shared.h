#pragma once

/**
 * @file
 *
 * The error reporting strategies of event_recorder.h, event_session.h,
 * and event_server.h are similar and use utility functions here. Also, the
 * event descriptor table mmap(2) strategy is shared by both the MPSC recorder
 * queue and consumer-facing queues
 */

#include <stdarg.h>
#include <stddef.h>

struct monad_event_ring;
typedef struct monad_source_location monad_source_location_t;

int _monad_event_vformat_err(
    char *error_buf, size_t size, monad_source_location_t const *srcloc,
    int err, char const *format, va_list ap);

typedef __attribute__((format(printf, 3, 4))) int(_monad_event_format_err_fn)(
    monad_source_location_t const *srcloc, int err, char const *format, ...);

enum monad_event_ring_type
{
    MONAD_EVENT_RING_TYPE_RECORDER,
    MONAD_EVENT_RING_TYPE_SHARED
};

int _monad_event_mmap_descriptor_table(
    enum monad_event_ring_type, uint8_t ring_shift, char const *ring_id,
    _monad_event_format_err_fn *err_fn, struct monad_event_descriptor **table,
    size_t *ring_capacity, int *fd);

void _monad_event_unmap_descriptor_table(
    struct monad_event_descriptor *, size_t ring_capacity);
