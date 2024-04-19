#pragma once

// Lockless shared memory single producer multiple consumer stream. It is the
// consumers responsibility to keep up with the producer. Sequence numbers start
// at 2 and increase by 2 on every message, unless a gap occurred.

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

#define SPMC_STREAM_MAX_PAYLOAD_SIZE 1014

struct SpmcStream;

struct SpmcStream *spmc_stream_create(char const *path, bool is_producer);

// returns
//    0 on success
//    EMSGSIZE if data is too large
int spmc_stream_write(struct SpmcStream *, void const *buf, size_t);
void spmc_stream_push(struct SpmcStream *);

// returns
//    0 on success
//    EAGAIN if no more elements to pop
//    ECANCELED if element was modified during on_payload
int spmc_stream_pop(
    struct SpmcStream *,
    void (*on_payload)(
        unsigned long long seq, void const volatile *, size_t, void *context),
    void *context);

void spmc_stream_destroy(struct SpmcStream *);

#ifdef __cplusplus
}
#endif
