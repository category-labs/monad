#pragma once

// #define MONAD_ASYNC_EXECUTOR_PRINTING 1

#include "task_impl.h"

#include "executor.h"

#include <monad/util/ticks_count_impl.h>

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <threads.h>

#include <execinfo.h>
#include <liburing.h>
#include <liburing/io_uring.h>
#include <linux/ioprio.h>
#include <poll.h>
#include <sys/eventfd.h>
#include <sys/mman.h>
#include <sys/resource.h> // for setrlimit
#include <unistd.h>

#if MONAD_HAVE_TSAN
    #include <sanitizer/tsan_interface.h>
#endif

typedef struct monad_async_file_head *monad_async_file;
typedef struct monad_async_socket_head *monad_async_socket;

struct monad_async_executor_free_registered_buffer
{
    struct monad_async_executor_free_registered_buffer *next;
    unsigned index;
};

LIST_DECLARE_N(struct monad_async_task_impl);
LIST_DECLARE_P(struct monad_async_task_impl);

struct monad_async_executor_impl
{
    struct monad_async_executor_head head;
    char magic[8];

    thrd_t owning_thread;
    bool within_run;
    MONAD_CPP_STD atomic_bool need_to_empty_eventfd;
    monad_context run_context;
    struct io_uring ring, wr_ring;
    unsigned wr_ring_ops_outstanding;
    LIST_DEFINE_P(tasks_running, struct monad_async_task_impl);
    LIST_DEFINE_P(
        tasks_suspended_submission_ring, struct monad_async_task_impl);
    LIST_DEFINE_P(
        tasks_suspended_submission_wr_ring, struct monad_async_task_impl);
    LIST_DEFINE_P(tasks_suspended_awaiting, struct monad_async_task_impl);
    LIST_DEFINE_P(tasks_suspended_completed, struct monad_async_task_impl);
    LIST_DEFINE_N(tasks_exited, struct monad_async_task_impl);
    MONAD_CPP_ATOMIC(monad_c_result *) cause_run_to_return;

    int *file_indices;

    struct monad_async_executor_impl_registered_buffers_t
    {
        struct iovec *buffers;
        unsigned size;

        struct
        {
            unsigned count, size;
            struct monad_async_executor_free_registered_buffer *free;

            struct io_uring_buf_ring *buf_ring;
            unsigned buf_ring_count;
            int buf_ring_mask;

            struct
            {
                struct io_buffer_awaiting_list_item_t *front, *back;
                size_t count;
            } tasks_awaiting;
        } buffer[2]; // small/large
    } registered_buffers[2]; // non-file-write ring/file write ring

    struct monad_async_executor_impl_max_io_concurrency_t
    {
        unsigned limit;
        struct max_concurrent_io_list_item_t *front, *back;
        size_t count;
    } max_io_concurrency;

    // all items below this require taking the lock
    MONAD_CPP_STD atomic_int lock;
    int eventfd;
    LIST_DEFINE_N(tasks_pending_launch, struct monad_async_task_impl);
    monad_c_result cause_run_to_return_value;
};

extern monad_c_result monad_async_executor_suspend_impl(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    monad_c_result (*please_cancel)(
        struct monad_async_executor_impl *ex,
        struct monad_async_task_impl *task),
    monad_async_io_status **completed,
    struct monad_async_task_impl *task_to_resume);

// diseased dead beef in hex, last three bits set
static uintptr_t const EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC =
    (uintptr_t)0xd15ea5eddeadbeef;

// dead beef in hex, last three bits set
static uintptr_t const CANCELLED_OP_IO_URING_DATA_MAGIC =
    (uintptr_t)0x00000000deadbeef;

// Cannot exceed three bits
enum io_uring_user_data_type : uint8_t
{
    io_uring_user_data_type_none = 0, // to detect misconfig
    io_uring_user_data_type_task = 1, // payload is a task ptr
    io_uring_user_data_type_iostatus = 2, // payload is an i/o status ptr
    io_uring_user_data_type_magic =
        7 // special values e.g. EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC
};

#ifndef __cplusplus

    #define io_uring_mangle_into_data(value)                                        \
        _Generic(                                                                   \
            (value),                                                                \
            struct                                                                  \
                monad_async_task_impl *: (void                                      \
                                              *)(((uintptr_t)(value)) |             \
                                                 io_uring_user_data_type_task),     \
            struct                                                                  \
                monad_async_io_status *: (void                                      \
                                              *)(((uintptr_t)(value)) |             \
                                                 io_uring_user_data_type_iostatus), \
            uintptr_t: (void *)(((uintptr_t)(value)) |                              \
                                io_uring_user_data_type_magic))

    #define io_uring_sqe_set_data(sqe, value, task, tofill)                    \
        io_uring_sqe_set_data((sqe), io_uring_mangle_into_data(value));        \
        assert(((sqe)->user_data & 7) != 0);                                   \
        assert(                                                                \
            ((sqe)->user_data & 7) == io_uring_user_data_type_magic ||         \
            ((uintptr_t)(value)) == ((sqe)->user_data & ~(uintptr_t)7));       \
        _Generic(                                                              \
            (value),                                                           \
            default: (void)0,                                                  \
            struct monad_async_io_status *: io_uring_set_up_io_status(         \
                                              (struct monad_async_io_status    \
                                                   *)(value),                  \
                                              (task),                          \
                                              (tofill)))

    #define io_uring_cqe_get_data(task, iostatus, magic, cqe)                  \
        switch (((uintptr_t)io_uring_cqe_get_data(cqe)) & 7) {                 \
        default: {                                                             \
            void *user_data = io_uring_cqe_get_data(cqe);                      \
            (void)user_data;                                                   \
            fprintf(                                                           \
                stderr,                                                        \
                "FATAL: io_uring cqe's user_data=%p which is an impossible "   \
                "value. res=%d flags=%u\n",                                    \
                user_data,                                                     \
                cqe->res,                                                      \
                cqe->flags);                                                   \
            abort();                                                           \
        }                                                                      \
        case io_uring_user_data_type_task:                                     \
            (task) = (struct monad_async_task_impl                             \
                          *)(((uintptr_t)io_uring_cqe_get_data(cqe)) &         \
                             ~(uintptr_t)7);                                   \
            (iostatus) = nullptr;                                              \
            (magic) = 0;                                                       \
            break;                                                             \
        case io_uring_user_data_type_iostatus:                                 \
            (task) = nullptr;                                                  \
            (iostatus) = (struct monad_async_io_status                         \
                              *)(((uintptr_t)io_uring_cqe_get_data(cqe)) &     \
                                 ~(uintptr_t)7);                               \
            (magic) = 0;                                                       \
            break;                                                             \
        case io_uring_user_data_type_magic:                                    \
            (task) = nullptr;                                                  \
            (iostatus) = nullptr;                                              \
            (magic) = (uintptr_t)io_uring_cqe_get_data(cqe);                   \
            break;                                                             \
        }

static inline void io_uring_set_up_io_status(
    struct monad_async_io_status *iostatus, struct monad_async_task_impl *task,
    struct monad_async_task_registered_io_buffer *tofill)
{
    iostatus->prev = iostatus->next = nullptr;
    iostatus->task_ = &task->head;
    iostatus->flags_ = (unsigned)-1;
    iostatus->tofill_ = tofill;
}

static inline void atomic_lock(atomic_int *lock)
{
    #if MONAD_HAVE_TSAN
    __tsan_mutex_pre_lock(lock, __tsan_mutex_try_lock);
    #endif
    int expected = 0;
    while (!atomic_compare_exchange_strong_explicit(
        lock, &expected, 1, memory_order_acq_rel, memory_order_relaxed)) {
        thrd_yield();
        expected = 0;
    }
    #if MONAD_HAVE_TSAN
    __tsan_mutex_post_lock(lock, __tsan_mutex_try_lock, 0);
    #endif
}

static inline void atomic_unlock(atomic_int *lock)
{
    #if MONAD_HAVE_TSAN
    __tsan_mutex_pre_unlock(lock, __tsan_mutex_try_lock);
    #endif
    atomic_store_explicit(lock, 0, memory_order_release);
    #if MONAD_HAVE_TSAN
    __tsan_mutex_post_unlock(lock, __tsan_mutex_try_lock);
    #endif
}

static inline int mutex_lock(mtx_t *lock)
{
    #if MONAD_HAVE_TSAN
    __tsan_mutex_pre_lock(lock, __tsan_mutex_try_lock);
    #endif
    int r = mtx_lock(lock);
    #if MONAD_HAVE_TSAN
    __tsan_mutex_post_lock(lock, __tsan_mutex_try_lock, 0);
    #endif
    return r;
}

static inline int mutex_unlock(mtx_t *lock)
{
    #if MONAD_HAVE_TSAN
    __tsan_mutex_pre_unlock(lock, __tsan_mutex_try_lock);
    #endif
    int r = mtx_unlock(lock);
    #if MONAD_HAVE_TSAN
    __tsan_mutex_post_unlock(lock, __tsan_mutex_try_lock);
    #endif
    return r;
}

static inline int64_t timespec_to_ns(const struct timespec *a)
{
    return ((int64_t)a->tv_sec * 1000000000LL) + (int64_t)a->tv_nsec;
}

static inline int64_t
timespec_diff(const struct timespec *a, const struct timespec *b)
{
    return timespec_to_ns(a) - timespec_to_ns(b);
}

static inline int infer_buffer_index_if_possible(
    struct monad_async_executor_impl *ex, const struct iovec *iovecs,
    size_t nr_vecs, bool is_write)
{
    if (ex->registered_buffers[is_write].buffers == nullptr || nr_vecs != 1) {
        return 0;
    }
    // This makes the big assumption that buffers[0] and
    // buffers[buffer_count[0]] are allocated in two single mmaps (see below)
    if (ex->registered_buffers[is_write].buffer[0].count > 0) {
        const struct iovec *begin_small =
            &ex->registered_buffers[is_write].buffers[0];
        const struct iovec *end_small =
            &ex->registered_buffers[is_write].buffers
                 [(ex->registered_buffers[is_write].buffer[0].count > 0)
                      ? (ex->registered_buffers[is_write].buffer[0].count - 1)
                      : 0];
        if (iovecs[0].iov_base >= begin_small->iov_base &&
            (char *)iovecs[0].iov_base <
                (char *)end_small->iov_base + end_small->iov_len) {
            int idx = (int)(((char *)iovecs[0].iov_base -
                             (char *)begin_small->iov_base) /
                            ex->registered_buffers[is_write].buffer[0].size);
            idx += 1;
            return is_write ? -idx : idx;
        }
    }
    if (ex->registered_buffers[is_write].buffer[1].count > 0) {
        const struct iovec *begin_large =
            &ex->registered_buffers[is_write]
                 .buffers[ex->registered_buffers[is_write].buffer[0].count];
        const struct iovec *end_large =
            &ex->registered_buffers[is_write]
                 .buffers[ex->registered_buffers[is_write].size - 1];
        if (iovecs[0].iov_base >= begin_large->iov_base &&
            (char *)iovecs[0].iov_base <
                (char *)end_large->iov_base + end_large->iov_len) {
            int idx = (int)(((char *)iovecs[0].iov_base -
                             (char *)begin_large->iov_base) /
                            ex->registered_buffers[is_write].buffer[1].size);
            idx += 1 + (int)ex->registered_buffers[is_write].buffer[0].count;
            return is_write ? -idx : idx;
        }
    }
    return 0;
}

static inline monad_c_result
monad_async_executor_create_impl_fill_registered_buffers(
    struct monad_async_executor_impl_registered_buffers_t *p,
    unsigned buffers_small_count, unsigned buffers_small_multiplier,
    unsigned buffers_large_count, unsigned buffers_large_multiplier)
{
    #ifndef NDEBUG
    if (buffers_small_count > (1U << 14) /*16384*/) {
        fprintf(
            stderr,
            "buffers_small_count > IORING_MAX_REG_BUFFERS, this will likely "
            "fail in release.\n");
        abort();
    }
    if (buffers_large_count > (1U << 14) /*16384*/) {
        fprintf(
            stderr,
            "buffers_large_count > IORING_MAX_REG_BUFFERS, this will likely "
            "fail in release.\n");
        abort();
    }
    #endif
    if (buffers_small_multiplier == 0) {
        buffers_small_multiplier = 1;
    }
    if (buffers_large_multiplier == 0) {
        buffers_large_multiplier = 1;
    }
    p->size = (buffers_small_count * buffers_small_multiplier) +
              (buffers_large_count * buffers_large_multiplier);
    if (p->size == 0) {
        return monad_c_make_success(0);
    }
    p->buffers = calloc(p->size, sizeof(struct iovec));
    if (p->buffers == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->buffer[0].count = buffers_small_count;
    p->buffer[1].count = buffers_large_count;
    p->buffer[0].size = buffers_small_multiplier * 4096u;
    p->buffer[1].size = buffers_large_multiplier * 2u * 1024u * 1024u;
    struct iovec *iov = p->buffers;
    if (buffers_small_count > 0) {
        size_t const buffer_length = p->buffer[0].size;
        void *const mem = mmap(
            nullptr,
            buffers_small_count * buffer_length,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0);
        if (mem == MAP_FAILED) {
            return monad_c_make_failure(errno);
        }
        for (unsigned n = 0; n < buffers_small_count; n++) {
            struct monad_async_executor_free_registered_buffer *i =
                (struct monad_async_executor_free_registered_buffer
                     *)((char *)mem + n * buffer_length);
            iov->iov_base = i;
            iov->iov_len = buffer_length;
            iov++;
            i->index = (unsigned)(iov - p->buffers);
            i->next = p->buffer[0].free;
            p->buffer[0].free = i;
        }
    }
    if (buffers_large_count > 0) {
        size_t const buffer_length = p->buffer[1].size;
        void *const mem = mmap(
            nullptr,
            buffers_large_count * buffer_length,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB |
                (21 << MAP_HUGE_SHIFT) /* 2Mb pages */,
            -1,
            0);
        if (mem == MAP_FAILED) {
            return monad_c_make_failure(errno);
        }
        for (unsigned n = 0; n < buffers_large_count; n++) {
            struct monad_async_executor_free_registered_buffer *i =
                (struct monad_async_executor_free_registered_buffer
                     *)((char *)mem + n * buffer_length);
            iov->iov_base = i;
            iov->iov_len = buffer_length;
            iov++;
            i->index = (unsigned)(iov - p->buffers);
            i->next = p->buffer[1].free;
            p->buffer[1].free = i;
        }
    }
    return monad_c_make_success(0);
}

static inline monad_c_result
monad_async_executor_setup_eventfd_polling(struct monad_async_executor_impl *p)
{
    struct io_uring_sqe *sqe = io_uring_get_sqe(&p->ring);
    if (sqe == nullptr) {
        abort(); // should never occur
    }
    // Do NOT increment total_io_submitted here!
    io_uring_prep_poll_multishot(sqe, p->eventfd, POLLIN);
    io_uring_sqe_set_data(
        sqe, EXECUTOR_EVENTFD_READY_IO_URING_DATA_MAGIC, nullptr, nullptr);
    int r = io_uring_submit(&p->ring);
    if (r < 0) {
        return monad_c_make_failure(-r);
    }
    return monad_c_make_success(0);
}

static inline monad_c_result monad_async_executor_create_impl(
    struct monad_async_executor_impl *p, struct monad_async_executor_attr *attr)
{
    p->owning_thread = thrd_current();
    p->max_io_concurrency.limit = attr->max_io_concurrency;
    p->eventfd = eventfd(0, EFD_CLOEXEC);
    if (-1 == p->eventfd) {
        return monad_c_make_failure(errno);
    }
    if (attr->io_uring_ring.entries > 0) {
        int r = io_uring_queue_init_params(
            attr->io_uring_ring.entries, &p->ring, &attr->io_uring_ring.params);
        if (r < 0) {
            return monad_c_make_failure(-r);
        }
        if (attr->io_uring_wr_ring.entries > 0) {
            r = io_uring_queue_init_params(
                attr->io_uring_wr_ring.entries,
                &p->wr_ring,
                &attr->io_uring_wr_ring.params);
            if (r < 0) {
                return monad_c_make_failure(-r);
            }
        }
        if (!(p->ring.features & IORING_FEAT_NODROP)) {
            fprintf(
                stderr,
                "FATAL: This kernel's io_uring implementation does not "
                "implement "
                "no-drop.\n");
            abort();
        }
        if (!(p->ring.features & IORING_FEAT_SUBMIT_STABLE)) {
            fprintf(
                stderr,
                "FATAL: This kernel's io_uring implementation does not "
                "implement "
                "stable submits.\n");
            abort();
        }
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
            monad_async_executor_setup_eventfd_polling(p));
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
            monad_async_executor_create_impl_fill_registered_buffers(
                &p->registered_buffers[0],
                attr->io_uring_ring.registered_buffers.small_count,
                attr->io_uring_ring.registered_buffers.small_multiplier,
                attr->io_uring_ring.registered_buffers.large_count,
                attr->io_uring_ring.registered_buffers.large_multiplier));
        if (p->registered_buffers[0].size > 0) {
            r = io_uring_register_buffers(
                &p->ring,
                p->registered_buffers[0].buffers,
                p->registered_buffers[0].size);
            if (r < 0) {
                return monad_c_make_failure(-r);
            }
            if (attr->io_uring_ring.registered_buffers
                    .small_kernel_allocated_count > 0) {
                if (attr->io_uring_ring.registered_buffers
                        .small_kernel_allocated_count >
                    p->registered_buffers[0].buffer[0].count) {
                    fprintf(
                        stderr,
                        "FATAL: small_kernel_allocated_count = %u is larger "
                        "than small_count = %u.\n",
                        attr->io_uring_ring.registered_buffers
                            .small_kernel_allocated_count,
                        attr->io_uring_ring.registered_buffers.small_count);
                    abort();
                }
                p->registered_buffers[0].buffer[0].buf_ring_count =
                    attr->io_uring_ring.registered_buffers
                        .small_kernel_allocated_count;
                int topbitset =
                    (int)(sizeof(unsigned) * __CHAR_BIT__) -
                    __builtin_clz(
                        p->registered_buffers[0].buffer[0].buf_ring_count);
                if ((1u << topbitset) !=
                    p->registered_buffers[0].buffer[0].buf_ring_count) {
                    topbitset++;
                }
                int ret = 0;
                p->registered_buffers[0].buffer[0].buf_ring =
                    io_uring_setup_buf_ring(
                        &p->ring, 1u << topbitset, 0, 0, &ret);
                if (p->registered_buffers[0].buffer[0].buf_ring == nullptr) {
                    return monad_c_make_failure(-ret);
                }
                p->registered_buffers[0].buffer[0].buf_ring_mask =
                    io_uring_buf_ring_mask(1u << topbitset);
                for (unsigned n = 0;
                     n < p->registered_buffers[0].buffer[0].buf_ring_count;
                     n++) {
                    struct monad_async_executor_free_registered_buffer *buff =
                        p->registered_buffers[0].buffer[0].free;
                    p->registered_buffers[0].buffer[0].free = buff->next;
                    io_uring_buf_ring_add(
                        p->registered_buffers[0].buffer[0].buf_ring,
                        buff,
                        p->registered_buffers[0].buffer[0].size,
                        (unsigned short)buff->index,
                        p->registered_buffers[0].buffer[0].buf_ring_mask,
                        (int)n);
                }
                io_uring_buf_ring_advance(
                    p->registered_buffers[0].buffer[0].buf_ring,
                    (int)p->registered_buffers[0].buffer[0].buf_ring_count);
            }
            if (attr->io_uring_ring.registered_buffers
                    .large_kernel_allocated_count > 0) {
                if (attr->io_uring_ring.registered_buffers
                        .large_kernel_allocated_count >
                    p->registered_buffers[0].buffer[1].count) {
                    fprintf(
                        stderr,
                        "FATAL: large_kernel_allocated_count = %u is larger "
                        "than large_count = %u.\n",
                        attr->io_uring_ring.registered_buffers
                            .large_kernel_allocated_count,
                        attr->io_uring_ring.registered_buffers.large_count);
                    abort();
                }
                p->registered_buffers[0].buffer[1].buf_ring_count =
                    attr->io_uring_ring.registered_buffers
                        .large_kernel_allocated_count;
                int topbitset =
                    (int)(sizeof(unsigned) * __CHAR_BIT__) -
                    __builtin_clz(
                        p->registered_buffers[0].buffer[1].buf_ring_count);
                if ((1u << topbitset) !=
                    p->registered_buffers[0].buffer[1].buf_ring_count) {
                    topbitset++;
                }
                int ret = 0;
                p->registered_buffers[0].buffer[1].buf_ring =
                    io_uring_setup_buf_ring(
                        &p->ring, 1u << topbitset, 1, 0, &ret);
                if (p->registered_buffers[0].buffer[1].buf_ring == nullptr) {
                    return monad_c_make_failure(-ret);
                }
                p->registered_buffers[0].buffer[1].buf_ring_mask =
                    io_uring_buf_ring_mask(1u << topbitset);
                for (unsigned n = 0;
                     n < p->registered_buffers[0].buffer[1].buf_ring_count;
                     n++) {
                    struct monad_async_executor_free_registered_buffer *buff =
                        p->registered_buffers[0].buffer[1].free;
                    p->registered_buffers[0].buffer[1].free = buff->next;
                    io_uring_buf_ring_add(
                        p->registered_buffers[0].buffer[1].buf_ring,
                        buff,
                        p->registered_buffers[0].buffer[1].size,
                        (unsigned short)buff->index,
                        p->registered_buffers[0].buffer[1].buf_ring_mask,
                        (int)n);
                }
                io_uring_buf_ring_advance(
                    p->registered_buffers[0].buffer[1].buf_ring,
                    (int)p->registered_buffers[0].buffer[1].count);
            }
        }
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
            monad_async_executor_create_impl_fill_registered_buffers(
                &p->registered_buffers[1],
                attr->io_uring_wr_ring.registered_buffers.small_count,
                attr->io_uring_wr_ring.registered_buffers.small_multiplier,
                attr->io_uring_wr_ring.registered_buffers.large_count,
                attr->io_uring_wr_ring.registered_buffers.large_multiplier));
        if (p->registered_buffers[1].size > 0) {
            r = io_uring_register_buffers(
                &p->wr_ring,
                p->registered_buffers[1].buffers,
                p->registered_buffers[1].size);
            if (r < 0) {
                return monad_c_make_failure(-r);
            }
        }
    }
    memcpy(p->magic, "MNASEXEC", 8);
    return monad_c_make_success(0);
}

static inline monad_c_result
monad_async_executor_destroy_impl(struct monad_async_executor_impl *ex)
{
    if (!thrd_equal(thrd_current(), ex->owning_thread)) {
        fprintf(
            stderr,
            "FATAL: You must destroy an executor from the same kernel "
            "thread "
            "which owns it.\n");
        abort();
    }
    // Any tasks still executing must be cancelled
    atomic_lock(&ex->lock);
    for (;;) {
        struct monad_async_task_impl *task = ex->tasks_pending_launch.front;
        if (task == nullptr) {
            break;
        }
        atomic_unlock(&ex->lock);
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
            monad_async_task_cancel(&ex->head, &task->head));
        atomic_lock(&ex->lock);
    }
    for (monad_async_priority priority = monad_async_priority_high;
         priority < monad_async_priority_max;
         priority++) {
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_running[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_suspended_awaiting[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
        for (;;) {
            struct monad_async_task_impl *task =
                ex->tasks_suspended_completed[priority].front;
            if (task == nullptr) {
                break;
            }
            atomic_unlock(&ex->lock);
            BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                monad_async_task_cancel(&ex->head, &task->head));
            atomic_lock(&ex->lock);
        }
    }
    atomic_unlock(&ex->lock);
    memset(ex->magic, 0, 8);
    if (ex->wr_ring.ring_fd != 0) {
        io_uring_queue_exit(&ex->wr_ring);
    }
    if (ex->ring.ring_fd != 0) {
        if (ex->registered_buffers[0].size > 0) {
            if (ex->registered_buffers[0].buffer[0].count > 0) {
                int topbitset =
                    (int)(sizeof(unsigned) * __CHAR_BIT__) -
                    __builtin_clz(ex->registered_buffers[0].buffer[0].count);
                if ((1u << topbitset) !=
                    ex->registered_buffers[0].buffer[0].count) {
                    topbitset++;
                }
                (void)io_uring_free_buf_ring(
                    &ex->ring,
                    ex->registered_buffers[0].buffer[0].buf_ring,
                    1u << topbitset,
                    0);
            }
            if (ex->registered_buffers[0].buffer[1].count > 0) {
                int topbitset =
                    (int)(sizeof(unsigned) * __CHAR_BIT__) -
                    __builtin_clz(ex->registered_buffers[0].buffer[1].count);
                if ((1u << topbitset) !=
                    ex->registered_buffers[0].buffer[1].count) {
                    topbitset++;
                }
                (void)io_uring_free_buf_ring(
                    &ex->ring,
                    ex->registered_buffers[0].buffer[1].buf_ring,
                    1u << topbitset,
                    1);
            }
        }
        io_uring_queue_exit(&ex->ring);
    }
    if (ex->eventfd != -1) {
        close(ex->eventfd);
        ex->eventfd = -1;
    }
    if (ex->file_indices != nullptr) {
        free(ex->file_indices);
        ex->file_indices = nullptr;
    }
    for (unsigned n = 0; n < ex->registered_buffers[0].size; n++) {
        (void)munmap(
            ex->registered_buffers[0].buffers[n].iov_base,
            ex->registered_buffers[0].buffers[n].iov_len);
    }
    if (ex->registered_buffers[0].buffers != nullptr) {
        free(ex->registered_buffers[0].buffers);
    }
    for (unsigned n = 0; n < ex->registered_buffers[1].size; n++) {
        (void)munmap(
            ex->registered_buffers[1].buffers[n].iov_base,
            ex->registered_buffers[1].buffers[n].iov_len);
    }
    if (ex->registered_buffers[1].buffers != nullptr) {
        free(ex->registered_buffers[1].buffers);
    }
    return monad_c_make_success(0);
}

static inline monad_c_result monad_async_executor_wake_impl(
    atomic_int * /*lock must be held on entry*/,
    struct monad_async_executor_impl *ex,
    monad_c_result const *cause_run_to_return)
{
    if (cause_run_to_return != nullptr) {
        ex->cause_run_to_return_value = *cause_run_to_return;
        atomic_store_explicit(
            &ex->cause_run_to_return,
            &ex->cause_run_to_return_value,
            memory_order_release);
    }
    atomic_store_explicit(
        &ex->need_to_empty_eventfd, true, memory_order_release);
    if (-1 == eventfd_write(ex->eventfd, 1)) {
        return monad_c_make_success(errno);
    }
    return monad_c_make_success(0);
}

// Cancellation for tasks waiting due to max i/o concurrency
static inline monad_c_result suspend_task_if_max_concurrent_io_cancel(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    assert(task->please_cancel_status != please_cancel_not_invoked);
    task->head.derived.result = monad_c_make_failure(ECANCELED);
    assert(
        atomic_load_explicit(
            &task->head.is_suspended_awaiting, memory_order_acquire) == true);
    atomic_store_explicit(
        &task->head.is_suspended_awaiting, false, memory_order_release);
    LIST_REMOVE(
        ex->tasks_suspended_awaiting[monad_async_task_effective_cpu_priority(
            task)],
        task,
        (size_t *)nullptr);
    task->head.ticks_when_suspended_completed =
        get_ticks_count(memory_order_relaxed);
    atomic_store_explicit(
        &task->head.is_suspended_completed, true, memory_order_release);
    LIST_APPEND(
        ex->tasks_suspended_completed[monad_async_task_effective_cpu_priority(
            task)],
        task,
        (size_t *)nullptr);
    return monad_c_make_success(0);
}

static inline monad_c_result suspend_task_if_max_concurrent_io(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    bool is_cancellation_point)
{
    uint64_t const current_io_concurrency =
        ex->head.total_io_submitted - ex->head.total_io_completed;
    if (ex->max_io_concurrency.count > 0 ||
        current_io_concurrency >= ex->max_io_concurrency.limit) {
        // If there are tasks suspended on max i/o concurrency and there is
        // spare capacity, suspend me and resume them directly for
        // efficiency
        struct monad_async_task_impl *task_to_resume = nullptr;
        if (ex->max_io_concurrency.count > 0 &&
            current_io_concurrency < ex->max_io_concurrency.limit) {
            task_to_resume = (struct monad_async_task_impl
                                  *)((char *)ex->max_io_concurrency.front -
                                     offsetof(
                                         struct monad_async_task_impl,
                                         max_concurrent_io_awaiting));
            assert(
                atomic_load_explicit(
                    &task_to_resume->head.is_suspended_awaiting,
                    memory_order_acquire) == true);
            task_to_resume->head.derived.result = monad_c_make_success(0);
            // Unlike anywhere else, tasks suspended due to max_concurrent_io
            // aren't suspended for any other reason so migrate them to the
            // suspended completed list
            atomic_store_explicit(
                &task_to_resume->head.is_suspended_awaiting,
                false,
                memory_order_release);
            LIST_REMOVE(
                ex->tasks_suspended_awaiting
                    [monad_async_task_effective_cpu_priority(task)],
                task_to_resume,
                (size_t *)nullptr);
            atomic_store_explicit(
                &task_to_resume->head.is_suspended_completed,
                true,
                memory_order_release);
            LIST_APPEND(
                ex->tasks_suspended_completed
                    [monad_async_task_effective_cpu_priority(task)],
                task_to_resume,
                (size_t *)nullptr);
        }
        LIST_APPEND(
            ex->max_io_concurrency,
            &task->max_concurrent_io_awaiting,
            (size_t *)nullptr);
    #if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p suspends task %p awaiting max concurrency "
            "current_io_concurrency = %lu tasks_awaiting.count=%zu\n",
            (void *)ex,
            (void *)task,
            current_io_concurrency,
            ex->max_io_concurrency.count);
        fflush(stdout);
    #endif
        BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(monad_async_executor_suspend_impl(
            ex,
            task,
            suspend_task_if_max_concurrent_io_cancel,
            nullptr,
            task_to_resume));
    #if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p resumes task %p awaiting max concurrency "
            "please_cancel_status=%d\n",
            (void *)ex,
            (void *)task,
            task->please_cancel_status);
        fflush(stdout);
    #endif
        LIST_REMOVE(
            ex->max_io_concurrency,
            &task->max_concurrent_io_awaiting,
            (size_t *)nullptr);
        if (is_cancellation_point &&
            task->please_cancel_status != please_cancel_not_invoked) {
            if (task->please_cancel_status < please_cancel_invoked_seen) {
                task->please_cancel_status = please_cancel_invoked_seen;
            }
            return monad_c_make_failure(ECANCELED);
        }
    }
    return monad_c_make_success(0);
}

struct get_sqe_suspending_if_necessary_flags
{
    bool is_cancellation_point;
    bool max_concurrent_io_pacing_already_done;
};

static inline struct io_uring_sqe *get_sqe_suspending_if_necessary_impl(
    struct io_uring *ring,
    struct list_define_p_monad_async_task_impl_t wait_list[],
    atomic_bool *wait_list_task_flag, struct monad_async_executor_impl *ex,
    struct monad_async_task_impl *task,
    const struct get_sqe_suspending_if_necessary_flags flags)
{
    if (ex->max_io_concurrency.limit > 0 &&
        !flags.max_concurrent_io_pacing_already_done) {
        monad_c_result r = suspend_task_if_max_concurrent_io(
            ex, task, flags.is_cancellation_point);
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
            if (!outcome_status_code_equal_generic(&r.error, ECANCELED)) {
                MONAD_CONTEXT_CHECK_RESULT(r);
            }
            return nullptr;
        }
    }

    struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
    struct monad_async_task_impl *newtask = nullptr;
    // If there is any higher or equal priority work waiting on a SQE, they
    // get first dibs
    if (sqe != nullptr) {
        ex->head.total_io_submitted++;
        for (uint8_t priority = monad_async_priority_high;
             priority <= monad_async_task_effective_cpu_priority(task);
             priority++) {
            if (wait_list[priority].count > 0) {
                newtask = wait_list[priority].front;
                break;
            }
        }
    }
    // Will we need to suspend?
    if (sqe == nullptr || newtask != nullptr) {
        atomic_store_explicit(
            &ex->head.current_task, nullptr, memory_order_release);
        task->please_cancel = nullptr;
        task->completed = nullptr;
        atomic_store_explicit(
            &task->head.is_running, false, memory_order_release);
        LIST_REMOVE_ATOMIC_COUNTER(
            ex->tasks_running[monad_async_task_effective_cpu_priority(task)],
            task,
            &ex->head.tasks_running);
        atomic_store_explicit(wait_list_task_flag, true, memory_order_release);
        LIST_APPEND_ATOMIC_COUNTER(
            wait_list[monad_async_task_effective_cpu_priority(task)],
            task,
            &ex->head.tasks_suspended_sqe_exhaustion);
        task->head.ticks_when_suspended_awaiting =
            get_ticks_count(memory_order_relaxed);
        task->head.total_ticks_executed +=
            task->head.ticks_when_suspended_awaiting -
            task->head.ticks_when_resumed;
    #if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p suspends task %p due to SQE exhaustion\n",
            (void *)ex,
            (void *)task);
        fflush(stdout);
    #endif
        atomic_load_explicit(
            &task->head.derived.context->switcher, memory_order_acquire)
            ->suspend_and_call_resume(
                task->head.derived.context,
                (newtask != nullptr) ? newtask->head.derived.context : nullptr);
        task->head.ticks_when_resumed = get_ticks_count(memory_order_relaxed);
        assert(atomic_load_explicit(wait_list_task_flag, memory_order_acquire));
        atomic_store_explicit(wait_list_task_flag, false, memory_order_release);
        LIST_REMOVE_ATOMIC_COUNTER(
            wait_list[monad_async_task_effective_cpu_priority(task)],
            task,
            &ex->head.tasks_suspended_sqe_exhaustion);
        atomic_store_explicit(
            &task->head.is_running, true, memory_order_release);
        LIST_APPEND_ATOMIC_COUNTER(
            ex->tasks_running[monad_async_task_effective_cpu_priority(task)],
            task,
            &ex->head.tasks_running);
        assert(
            atomic_load_explicit(
                &ex->head.current_task, memory_order_acquire) == nullptr);
        atomic_store_explicit(
            &ex->head.current_task, &task->head, memory_order_release);
        // Do NOT reset please_cancel_invoked
        task->please_cancel = nullptr;
        task->completed = nullptr;

        // The SQE will have already been fetched by the code resuming us,
        // so we just need to "peek" the current SQE
        struct io_uring_sq *sq = &ring->sq;
        sqe = &sq->sqes[(sq->sqe_tail - 1) & *sq->kring_mask];
    #if MONAD_ASYNC_EXECUTOR_PRINTING
        printf(
            "*** Executor %p resumes task %p from SQE exhaustion. sqe=%p. "
            "is_cancellation_point=%d. please_cancel_status=%d\n",
            (void *)ex,
            (void *)task,
            (void *)sqe,
            flags.is_cancellation_point,
            task->please_cancel_status);
        fflush(stdout);
    #endif
        if (flags.is_cancellation_point &&
            task->please_cancel_status != please_cancel_not_invoked) {
            // We need to "throw away" this SQE, as the task has been
            // cancelled We do this by setting the SQE to a noop with
            // CANCELLED_OP_IO_URING_DATA_MAGIC
            io_uring_prep_nop(sqe);
            io_uring_sqe_set_data(
                sqe, CANCELLED_OP_IO_URING_DATA_MAGIC, task, nullptr);
            if (ring == &ex->wr_ring) {
                // This line took a few hours to figure out
                ex->wr_ring_ops_outstanding++;
            }
            return nullptr;
        }
    }

    /* This is quite possibly the hardest won line in this entire codebase.
    One was seeing spurious additional CQEs being returned with user_data
    values from a random previous CQE when cancelling an operation. Working
    around this was expensive and painful, as user_data values pointed into
    memory and there was no way of easily telling if a CQE userdata was
    valid or not.

    It turns out that the cause requires three conditions:

    1. The op needs to be one which does not use the SQE user_data to set
    the SQE user data, with the cancellation ops being these (they use
    the addr field instead for no obvious reason).
    2. io_uring_get_sqe() doesn't touch the user_data field, so if you
    happen to get a SQE with a user_data value set from last time, it gets
    sent again.
    3. io_uring then MAY elect to send a spurious additional CQE with the
    stale user_data but ONLY if the value is non-zero.

    Setting the user_data to zero on SQE allocation therefore eliminates
    the spurious CQE problem entirely.
    */
    sqe->user_data = 0;
    return sqe;
}

static inline struct io_uring_sqe *get_sqe_suspending_if_necessary(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    const struct get_sqe_suspending_if_necessary_flags flags)
{
    if (ex == nullptr ||
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) !=
            &task->head) {
        fprintf(
            stderr,
            "FATAL: Suspending operation invoked not by the "
            "current task executing.\n");
        abort();
    }
    assert(ex->within_run == true);
    assert(ex->ring.ring_fd != 0); // was the ring created?
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary_impl(
        &ex->ring,
        ex->tasks_suspended_submission_ring,
        &task->head.is_suspended_sqe_exhaustion,
        ex,
        task,
        flags);
    if (sqe == nullptr) {
        return nullptr;
    }
    switch (task->head.priority.io) {
    default:
        break;
    case monad_async_priority_high:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case monad_async_priority_low:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    }
    return sqe;
}

static inline struct io_uring_sqe *get_wrsqe_suspending_if_necessary(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task,
    const struct get_sqe_suspending_if_necessary_flags flags)
{
    if (ex == nullptr ||
        atomic_load_explicit(&ex->head.current_task, memory_order_acquire) !=
            &task->head) {
        fprintf(
            stderr,
            "FATAL: Suspending operation invoked not by the "
            "current task executing.\n");
        abort();
    }
    assert(ex->within_run == true);
    assert(ex->wr_ring.ring_fd != 0); // was the write ring created?
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary_impl(
        &ex->wr_ring,
        ex->tasks_suspended_submission_wr_ring,
        &task->head.is_suspended_sqe_exhaustion_wr,
        ex,
        task,
        flags);
    if (sqe == nullptr) {
        return nullptr;
    }
    switch (task->head.priority.io) {
    default:
        break;
    case monad_async_priority_high:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case monad_async_priority_low:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    }
    // The write ring must always complete the preceding operation before it
    // initiates the next operation
    sqe->flags |= IOSQE_IO_DRAIN;
    ex->wr_ring_ops_outstanding++;
    return sqe;
}

static inline struct io_uring_sqe *
get_sqe_for_cancellation(struct monad_async_executor_impl *ex)
{
    struct monad_async_task_impl *current_task =
        (struct monad_async_task_impl *)atomic_load_explicit(
            &ex->head.current_task, memory_order_acquire);
    if (current_task != nullptr) {
        // We are within the executor
        struct get_sqe_suspending_if_necessary_flags const flags = {
            .is_cancellation_point = false,
            .max_concurrent_io_pacing_already_done = true};
        return get_sqe_suspending_if_necessary(ex, current_task, flags);
    }
    // We are outside the executor
    for (;;) {
        struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->ring);
        if (sqe != nullptr) {
            ex->head.total_io_submitted++;
            return sqe;
        }
        io_uring_submit(&ex->ring);
    }
}

static inline struct io_uring_sqe *
get_wrsqe_for_cancellation(struct monad_async_executor_impl *ex)
{
    struct monad_async_task_impl *current_task =
        (struct monad_async_task_impl *)atomic_load_explicit(
            &ex->head.current_task, memory_order_acquire);
    if (current_task != nullptr) {
        // We are within the executor
        struct get_sqe_suspending_if_necessary_flags const flags = {
            .is_cancellation_point = false,
            .max_concurrent_io_pacing_already_done = true};
        struct io_uring_sqe *sqe =
            get_wrsqe_suspending_if_necessary(ex, current_task, flags);
        // Do NOT set IOSQE_IO_DRAIN, otherwise cancellation doesn't work!
        sqe->flags &= (__u8)(~IOSQE_IO_DRAIN);
        return sqe;
    }
    // We are outside the executor
    for (;;) {
        struct io_uring_sqe *sqe = io_uring_get_sqe(&ex->wr_ring);
        if (sqe != nullptr) {
            // Do NOT set IOSQE_IO_DRAIN, otherwise cancellation doesn't work!
            ex->wr_ring_ops_outstanding++;
            ex->head.total_io_submitted++;
            return sqe;
        }
        io_uring_submit(&ex->wr_ring);
    }
}

// If fd = -1, then he wants a new unallocated slot
static inline unsigned monad_async_executor_alloc_file_index(
    struct monad_async_executor_impl *ex, int fd)
{
    static rlim_t maxfds;
    if (fd == -1) {
        fd = -2;
    }
    if (ex->file_indices == nullptr) {
        if (maxfds == 0) {
            for (maxfds = 4096; maxfds >= 1024; maxfds >>= 1) {
                struct rlimit const r = {maxfds, maxfds};
                int const ret = setrlimit(RLIMIT_NOFILE, &r);
                if (ret >= 0) {
                    break;
                }
            }
            if (maxfds < 4096) {
                fprintf(
                    stderr,
                    "WARNING: maximum hard file descriptor kimit is %lu "
                    "which is less than 4096. 'Too many open files' "
                    "errors may result. You can increase the hard "
                    "file descriptor limit for a given user by adding "
                    "to '/etc/security/limits.conf' '<username> hard "
                    "nofile 16384'.\n",
                    maxfds);
            }
        }
        ex->file_indices = calloc(maxfds, sizeof(int));
        if (ex->file_indices == nullptr) {
            return (unsigned)-1;
        }
        memset(ex->file_indices, 0xff, maxfds * sizeof(int));
        int r = io_uring_register_files_sparse(&ex->ring, (unsigned)maxfds);
        if (r < 0) {
            fprintf(
                stderr,
                "FATAL: io_uring_register_files_sparse fails with '%s'\n",
                strerror(-r));
            abort();
        }
        if (ex->wr_ring.ring_fd != 0) {
            r = io_uring_register_files_sparse(&ex->wr_ring, (unsigned)maxfds);
            if (r < 0) {
                fprintf(
                    stderr,
                    "FATAL: io_uring_register_files_sparse (write ring) "
                    "fails "
                    "with "
                    "'%s'\n",
                    strerror(-r));
                abort();
            }
        }
    }
    for (rlim_t n = 0; n < maxfds; n++) {
        if (ex->file_indices[n] == -1) {
            ex->file_indices[n] = fd;
            if (fd >= 0) {
                int r = io_uring_register_files_update(
                    &ex->ring, (unsigned)n, &fd, 1);
                if (r < 0) {
                    fprintf(
                        stderr,
                        "FATAL: io_uring_register_files_update fails with "
                        "'%s'\n",
                        strerror(-r));
                    abort();
                }
                if (ex->wr_ring.ring_fd != 0) {
                    r = io_uring_register_files_update(
                        &ex->wr_ring, (unsigned)n, &fd, 1);
                    if (r < 0) {
                        fprintf(
                            stderr,
                            "FATAL: io_uring_register_files_update (write "
                            "ring) fails "
                            "with "
                            "'%s'\n",
                            strerror(-r));
                        abort();
                    }
                }
            }
            return (unsigned)n;
        }
    }
    fprintf(
        stderr,
        "FATAL: More than %lu io_uring file descriptor slots have been "
        "consumed.\n",
        maxfds);
    abort();
}

static inline void monad_async_executor_free_file_index(
    struct monad_async_executor_impl *ex, unsigned file_index)
{
    assert(ex->file_indices[file_index] != -1);
    ex->file_indices[file_index] = -1;
}

#endif
