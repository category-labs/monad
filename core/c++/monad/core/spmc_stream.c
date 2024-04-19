#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/spmc_stream.h>

#include <errno.h>
#include <fcntl.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

static_assert(ATOMIC_LLONG_LOCK_FREE == 2);

typedef struct SpmcStreamElement
{
    atomic_ullong seq;
    uint16_t size;
    char payload[SPMC_STREAM_MAX_PAYLOAD_SIZE];
} SpmcStreamElement;

static_assert(sizeof(SpmcStreamElement) == 1024);
static_assert(alignof(SpmcStreamElement) == 8);

typedef struct SpmcStreamRegion
{
    SpmcStreamElement volatile buf[512];
} SpmcStreamRegion;

static_assert(sizeof(SpmcStreamRegion) == 524288);
static_assert(alignof(SpmcStreamRegion) == 8);

typedef struct SpmcStream
{
    char *path;
    bool is_producer;
    unsigned long long seq;
    SpmcStreamRegion *shm;
} SpmcStream;

static_assert(sizeof(SpmcStream) == 32);
static_assert(alignof(SpmcStream) == 8);

SpmcStream *spmc_stream_create(char const *const path, bool const is_producer)
{
    int const fd = shm_open(
        path,
        is_producer ? O_CREAT | O_EXCL | O_RDWR : O_RDONLY,
        is_producer ? S_IRUSR : 0);
    if (fd == -1) {
        return NULL;
    }

    if (is_producer) {
        MONAD_ASSERT(flock(fd, LOCK_EX | LOCK_NB) == 0);
        if (ftruncate(fd, sizeof(SpmcStreamRegion)) == -1) {
            return NULL;
        }
    }
    else {
        MONAD_ASSERT(flock(fd, LOCK_SH) == 0);
        struct stat stat;
        MONAD_ASSERT(fstat(fd, &stat) == 0);
        MONAD_ASSERT(stat.st_size == sizeof(SpmcStreamRegion));
    }

    SpmcStreamRegion *const shm = mmap(
        NULL,
        sizeof(SpmcStreamRegion),
        is_producer ? PROT_READ | PROT_WRITE : PROT_READ,
        MAP_SHARED,
        fd,
        0);
    if (shm == MAP_FAILED) {
        return NULL;
    }

    if (is_producer) {
        atomic_init(&shm->buf[0].seq, 1);
        for (size_t i = 1;
             i < (sizeof(SpmcStreamRegion) / sizeof(SpmcStreamElement));
             ++i) {
            atomic_init(&shm->buf[i].seq, 0);
        }
    }

    SpmcStream *queue = malloc(sizeof(*queue));
    queue->path = malloc(strlen(path) + 1);
    strcpy(queue->path, path);
    queue->is_producer = is_producer;
    queue->seq = 0;
    queue->shm = shm;

    MONAD_ASSERT(flock(fd, LOCK_UN) == 0);

    return queue;
}

int spmc_stream_write(
    SpmcStream *const queue, void const *const buf, size_t const size)
{
    MONAD_ASSERT(queue != NULL);
    MONAD_ASSERT(queue->is_producer);

    if (MONAD_UNLIKELY(size > SPMC_STREAM_MAX_PAYLOAD_SIZE)) {
        return EMSGSIZE;
    }

    unsigned long long const idx =
        (queue->seq / 2) %
        (sizeof(SpmcStreamRegion) / sizeof(SpmcStreamElement));
    SpmcStreamElement volatile *const shm = &queue->shm->buf[idx];
    if ((queue->seq % 2) == 0) {
        ++queue->seq;
        atomic_store_explicit(&shm->seq, queue->seq, memory_order_release);
        shm->size = 0;
    }
    if (MONAD_UNLIKELY((shm->size + size) > SPMC_STREAM_MAX_PAYLOAD_SIZE)) {
        return EMSGSIZE;
    }
    for (size_t i = 0; i < size; ++i) {
        shm->payload[shm->size + i] = ((char const *)buf)[i];
    }
    shm->size += (uint16_t)size;

    MONAD_ASSERT(queue->seq % 2);
    MONAD_ASSERT(atomic_load_explicit(&shm->seq, memory_order_relaxed) % 2);
    return 0;
}

void spmc_stream_push(SpmcStream *const queue)
{
    MONAD_ASSERT(queue != NULL);
    MONAD_ASSERT(queue->is_producer);
    MONAD_ASSERT(queue->seq % 2);

    unsigned long long const idx =
        (queue->seq / 2) %
        (sizeof(SpmcStreamRegion) / sizeof(SpmcStreamElement));
    SpmcStreamElement volatile *const shm = &queue->shm->buf[idx];
    MONAD_ASSERT(atomic_load_explicit(&shm->seq, memory_order_relaxed) % 2);
    ++queue->seq;
    atomic_store_explicit(&shm->seq, queue->seq, memory_order_release);

    MONAD_ASSERT((queue->seq % 2) == 0);
    MONAD_ASSERT(
        (atomic_load_explicit(&shm->seq, memory_order_relaxed) % 2) == 0);
}

int spmc_stream_pop(
    SpmcStream *const queue,
    void (*on_payload)(
        unsigned long long seq, void const volatile *, size_t, void *context),
    void *context)
{
    MONAD_ASSERT(queue != NULL);
    MONAD_ASSERT(!queue->is_producer);
    MONAD_ASSERT((queue->seq % 2) == 0);

    unsigned long long const idx =
        (queue->seq / 2) %
        (sizeof(SpmcStreamRegion) / sizeof(SpmcStreamElement));
    SpmcStreamElement const volatile *const shm = &queue->shm->buf[idx];
    unsigned long long const seq =
        atomic_load_explicit(&shm->seq, memory_order_acquire);
    if (MONAD_UNLIKELY(seq < queue->seq)) {
        return EAGAIN;
    }
    else if (MONAD_UNLIKELY((seq % 2) == 1)) {
        MONAD_ASSERT(seq > queue->seq);
        return EAGAIN;
    }
    on_payload(seq, shm->payload, shm->size, context);
    unsigned long long const nseq =
        atomic_load_explicit(&shm->seq, memory_order_acquire);
    if (MONAD_UNLIKELY(seq != nseq)) {
        MONAD_ASSERT(seq < nseq);
        return ECANCELED;
    }
    queue->seq = seq;
    return 0;
}

void spmc_stream_destroy(SpmcStream *const queue)
{
    MONAD_ASSERT(queue != NULL);
    MONAD_ASSERT(munmap((void *)queue->shm, sizeof(SpmcStreamRegion)) == 0);
    if (queue->is_producer) {
        MONAD_ASSERT(shm_unlink(queue->path) == 0);
    }
    free(queue->path);
    free(queue);
}
