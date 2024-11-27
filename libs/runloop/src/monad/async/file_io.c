#include "file_io.h"

// #define MONAD_ASYNC_FILE_IO_PRINTING 1

#include <monad/context/boost_result.h>
#include <monad/context/config.h>

#include "executor.h"
#include "executor_impl.h"
#include "task_impl.h"

#include <errno.h>
#include <stdatomic.h>

#include <fcntl.h>

struct monad_async_file_impl
{
    struct monad_async_file_head head;
    char magic[8];
    unsigned io_uring_file_index_read; // NOT a traditional file descriptor!
    unsigned io_uring_file_index_write; // NOT a traditional file descriptor!
};

static inline monad_c_result monad_async_task_file_create_cancel1(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    struct io_uring_sqe *sqe = get_sqe_for_cancellation(ex);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(task), 0);
    sqe->user_data = (__u64)io_uring_mangle_into_data(task);
#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates cancel "
        "file_open\n",
        (void *)task,
        (void *)ex);
    fflush(stdout);
#endif
    return monad_c_make_failure(EAGAIN); // Canceller needs to wait
}

static inline monad_c_result monad_async_task_file_create_cancel2(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    struct io_uring_sqe *sqe = get_wrsqe_for_cancellation(ex);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(task), 0);
    sqe->user_data = (__u64)io_uring_mangle_into_data(task);
#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates cancel "
        "file_open (write ring)\n",
        (void *)task,
        (void *)ex);
    fflush(stdout);
#endif
    return monad_c_make_failure(EAGAIN); // Canceller needs to wait
}

monad_c_result monad_async_task_file_create(
    monad_async_file *file, monad_async_task task_, monad_async_file base,
    char const *subpath, struct open_how *how)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    struct monad_async_file_impl *p = (struct monad_async_file_impl *)calloc(
        1, sizeof(struct monad_async_file_impl));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->head.executor = &ex->head;
    p->io_uring_file_index_read = (unsigned)-1;
    p->io_uring_file_index_write = (unsigned)-1;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return monad_c_make_failure(ECANCELED);
    }
    unsigned file_index = monad_async_executor_alloc_file_index(ex, -1);
    if (file_index == (unsigned)-1) {
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return monad_c_make_failure(ENOMEM);
    }
    struct get_sqe_suspending_if_necessary_flags const flags = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task, flags);
    if (sqe == nullptr) {
        assert(task->please_cancel_status != please_cancel_not_invoked);
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return monad_c_make_failure(ECANCELED);
    }
    io_uring_prep_openat2_direct(
        sqe,
        (base == nullptr) ? AT_FDCWD
                          : (int)((struct monad_async_file_impl *)base)
                                ->io_uring_file_index_read,
        subpath,
        how,
        file_index);
    io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_open\n",
        (void *)task,
        (void *)ex);
    fflush(stdout);
#endif
    monad_c_result ret = monad_async_executor_suspend_impl(
        ex, task, monad_async_task_file_create_cancel1, nullptr, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "file_open with file_index=%u and ret=%s\n",
        (void *)task,
        (void *)ex,
        file_index,
        BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)
            ? outcome_status_code_message(&ret.error)
            : "success");
    fflush(stdout);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        monad_async_executor_free_file_index(ex, file_index);
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return ret;
    }
    p->io_uring_file_index_read = file_index;

    if (ex->wr_ring.ring_fd != 0) {
        struct get_sqe_suspending_if_necessary_flags const flags = {
            .is_cancellation_point = true,
            .max_concurrent_io_pacing_already_done = false};
        sqe = get_wrsqe_suspending_if_necessary(ex, task, flags);
        if (sqe == nullptr) {
            assert(task->please_cancel_status != please_cancel_not_invoked);
            (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
            return monad_c_make_failure(ECANCELED);
        }
        io_uring_prep_openat2_direct(
            sqe,
            (base == nullptr) ? AT_FDCWD
                              : (int)((struct monad_async_file_impl *)base)
                                    ->io_uring_file_index_read,
            subpath,
            how,
            file_index);
        io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_FILE_IO_PRINTING
        printf(
            "*** Task %p running on executor %p initiates "
            "file_open (write ring)\n",
            (void *)task,
            (void *)ex);
        fflush(stdout);
#endif
        monad_c_result ret = monad_async_executor_suspend_impl(
            ex, task, monad_async_task_file_create_cancel2, nullptr, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
        printf(
            "*** Task %p running on executor %p completes "
            "file_open (write ring) with file_index=%u and ret=%s\n",
            (void *)task,
            (void *)ex,
            file_index,
            BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)
                ? outcome_status_code_message(&ret.error)
                : "success");
        fflush(stdout);
#endif
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
            (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
            return ret;
        }
        p->io_uring_file_index_write = file_index;
    }
    memcpy(p->magic, "MNASFILE", 8);
    *file = (monad_async_file)p;
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_file_create_from_existing_fd(
    monad_async_file *file, monad_async_task task_, int fd)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    struct monad_async_file_impl *p = (struct monad_async_file_impl *)calloc(
        1, sizeof(struct monad_async_file_impl));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->head.executor = &ex->head;
    p->io_uring_file_index_read = (unsigned)-1;
    p->io_uring_file_index_write = (unsigned)-1;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return monad_c_make_failure(ECANCELED);
    }
    unsigned file_index = monad_async_executor_alloc_file_index(ex, fd);
    if (file_index == (unsigned)-1) {
        (void)monad_async_task_file_destroy(task_, (monad_async_file)p);
        return monad_c_make_failure(ENOMEM);
    }
    p->io_uring_file_index_read = file_index;
    if (ex->wr_ring.ring_fd != 0) {
        p->io_uring_file_index_write = file_index;
    }
    memcpy(p->magic, "MNASFILE", 8);
    *file = (monad_async_file)p;
    return monad_c_make_success(0);
}

monad_c_result
monad_async_task_file_destroy(monad_async_task task_, monad_async_file file_)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    if (file->io_uring_file_index_read != (unsigned)-1) {
        struct monad_async_task_impl *task =
            (struct monad_async_task_impl *)task_;
        struct monad_async_executor_impl *ex =
            (struct monad_async_executor_impl *)atomic_load_explicit(
                &task_->current_executor, memory_order_acquire);
        if (ex == nullptr) {
            return monad_c_make_failure(EINVAL);
        }
        if (file->io_uring_file_index_write != (unsigned)-1) {
            struct get_sqe_suspending_if_necessary_flags const flags = {
                .is_cancellation_point = false,
                .max_concurrent_io_pacing_already_done = false};
            struct io_uring_sqe *sqe =
                get_wrsqe_suspending_if_necessary(ex, task, flags);
            io_uring_prep_close(sqe, 0);
            __io_uring_set_target_fixed_file(
                sqe, file->io_uring_file_index_write);
            io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_FILE_IO_PRINTING
            printf(
                "*** Task %p running on executor %p initiates "
                "file_close (write ring)\n",
                (void *)task,
                (void *)ex);
            fflush(stdout);
#endif
            monad_c_result ret = monad_async_executor_suspend_impl(
                ex, task, nullptr, nullptr, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
            printf(
                "*** Task %p running on executor %p completes "
                "file_close (write ring) for file_index=%u\n",
                (void *)task,
                (void *)ex,
                file->io_uring_file_index_write);
            fflush(stdout);
#endif
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
                return ret;
            }
        }
        struct get_sqe_suspending_if_necessary_flags const flags = {
            .is_cancellation_point = false,
            .max_concurrent_io_pacing_already_done = false};
        struct io_uring_sqe *sqe =
            get_sqe_suspending_if_necessary(ex, task, flags);
        io_uring_prep_close(sqe, 0);
        __io_uring_set_target_fixed_file(sqe, file->io_uring_file_index_read);
        io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_FILE_IO_PRINTING
        printf(
            "*** Task %p running on executor %p initiates "
            "file_close\n",
            (void *)task,
            (void *)ex);
        fflush(stdout);
#endif
        monad_c_result ret = monad_async_executor_suspend_impl(
            ex, task, nullptr, nullptr, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
        printf(
            "*** Task %p running on executor %p completes "
            "file_close for file_index=%u\n",
            (void *)task,
            (void *)ex,
            file->io_uring_file_index_read);
        fflush(stdout);
#endif
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
            return ret;
        }
        memset(ex->magic, 0, 8);
        monad_async_executor_free_file_index(
            ex, file->io_uring_file_index_read);
    }
    free(file);
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_file_fallocate(
    monad_async_task task_, monad_async_file file_, int mode,
    monad_async_file_offset offset, monad_async_file_offset len)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        return monad_c_make_failure(ECANCELED);
    }
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    if (file->io_uring_file_index_write == (unsigned)-1) {
        return monad_c_make_failure(EBADF);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    struct get_sqe_suspending_if_necessary_flags const flags = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_wrsqe_suspending_if_necessary(ex, task, flags);
    if (sqe == nullptr) {
        return monad_c_make_failure(ECANCELED);
    }
#if !defined(IO_URING_VERSION_MAJOR)
    io_uring_prep_fallocate(
        sqe, (int)file->io_uring_file_index, mode, (off_t)offset, (off_t)len);
#else
    io_uring_prep_fallocate(
        sqe, (int)file->io_uring_file_index_write, mode, offset, len);
#endif
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_allocate\n",
        (void *)task,
        (void *)ex);
    fflush(stdout);
#endif
    monad_c_result ret =
        monad_async_executor_suspend_impl(ex, task, nullptr, nullptr, nullptr);
#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "file_allocate for file_index=%u\n",
        (void *)task,
        (void *)ex,
        file->io_uring_file_index_write);
    fflush(stdout);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        return ret;
    }
    return monad_c_make_success(0);
}

static inline monad_c_result monad_async_task_file_io_cancel(
    monad_async_task task_, monad_async_io_status *iostatus)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_for_cancellation(ex);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(iostatus), 0);
    sqe->user_data = (__u64)io_uring_mangle_into_data(iostatus);
    return monad_c_make_success(EAGAIN); // Canceller needs to wait
}

static inline monad_c_result monad_async_task_file_wrio_cancel(
    monad_async_task task_, monad_async_io_status *iostatus)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_wrsqe_for_cancellation(ex);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(iostatus), 0);
    sqe->user_data = (__u64)io_uring_mangle_into_data(iostatus);
    return monad_c_make_success(EAGAIN); // Canceller needs to wait
}

void monad_async_task_file_read(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_,
    struct monad_async_task_registered_io_buffer *tofill, size_t max_bytes,
    monad_async_file_offset offset, int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    assert(
        ex->registered_buffers[0].buffers !=
        nullptr); // use readv() if you haven't set up buffers
    assert(
        tofill->iov[0].iov_base == nullptr); // io_uring allocates this for you!

    // Prevent registered i/o buffer consumption blowout by pacing before buffer
    // allocation
    if (ex->max_io_concurrency.limit > 0) {
        monad_c_result r = suspend_task_if_max_concurrent_io(ex, task, false);
        MONAD_CONTEXT_CHECK_RESULT(r);
    }

    int buffer_index = 0;
    const struct monad_async_task_claim_registered_io_buffer_flags flags_ = {
        .fail_dont_suspend = false, ._for_read_ring = true};
    monad_c_result r = monad_async_task_claim_registered_file_io_write_buffer(
        tofill, task_, max_bytes, flags_);
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
        if (!outcome_status_code_equal_generic(&r.error, EINVAL) &&
            !outcome_status_code_equal_generic(&r.error, ECANCELED)) {
            MONAD_CONTEXT_CHECK_RESULT(r);
        }
        tofill->index = 0;
    }
    else {
        buffer_index = tofill->index - 1;
    }
    struct get_sqe_suspending_if_necessary_flags const sqeflags = {
        .is_cancellation_point = false,
        .max_concurrent_io_pacing_already_done = true};
    struct io_uring_sqe *sqe =
        get_sqe_suspending_if_necessary(ex, task, sqeflags);
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    io_uring_prep_read_fixed(
        sqe,
        (int)file->io_uring_file_index_read,
        tofill->iov[0].iov_base,
        (unsigned)max_bytes,
        offset,
        buffer_index);
    sqe->rw_flags = flags;
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, tofill);
    iostatus->cancel_ = monad_async_task_file_io_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_read on i/o status %p buffer_index=%d max_bytes=%zu "
        "offset=%lu\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus,
        buffer_index,
        max_bytes,
        offset);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_readv(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_, const struct iovec *iovecs, unsigned nr_vecs,
    monad_async_file_offset offset, int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    struct get_sqe_suspending_if_necessary_flags const flags_ = {
        .is_cancellation_point = false,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_sqe_suspending_if_necessary(ex, task, flags_);
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    int const buffer_index =
        infer_buffer_index_if_possible(ex, iovecs, nr_vecs, false);
    if (buffer_index == 0) {
        if (nr_vecs != 1) {
            io_uring_prep_readv(
                sqe,
                (int)file->io_uring_file_index_read,
                iovecs,
                nr_vecs,
                offset);
            sqe->rw_flags = flags;
        }
        else {
            io_uring_prep_read(
                sqe,
                (int)file->io_uring_file_index_read,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset);
        }
    }
    else {
        assert(buffer_index > 0);
        if (nr_vecs != 1) {
            assert(false);
            abort();
        }
        else {
            io_uring_prep_read_fixed(
                sqe,
                (int)file->io_uring_file_index_read,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset,
                buffer_index - 1);
            sqe->rw_flags = flags;
        }
    }
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_file_io_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_read_scatter on i/o status %p buffer_index=%d max_bytes=%zu "
        "offset=%lu\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus,
        buffer_index,
        iovecs[0].iov_len,
        offset);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_write(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_, int buffer_index, const struct iovec *iovecs,
    unsigned nr_vecs, monad_async_file_offset offset, int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    struct get_sqe_suspending_if_necessary_flags const flags_ = {
        .is_cancellation_point = false,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_wrsqe_suspending_if_necessary(ex, task, flags_);
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    if (buffer_index == 0) {
        buffer_index =
            infer_buffer_index_if_possible(ex, iovecs, nr_vecs, true);
    }
    if (buffer_index == 0) {
        if (nr_vecs != 1) {
            io_uring_prep_writev(
                sqe,
                (int)file->io_uring_file_index_write,
                iovecs,
                nr_vecs,
                offset);
            sqe->rw_flags = flags;
        }
        else {
            io_uring_prep_write(
                sqe,
                (int)file->io_uring_file_index_write,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset);
        }
    }
    else {
        assert(buffer_index < 0);
        if (nr_vecs != 1) {
            assert(false);
            abort();
        }
        else {
            io_uring_prep_write_fixed(
                sqe,
                (int)file->io_uring_file_index_write,
                iovecs[0].iov_base,
                (unsigned)iovecs[0].iov_len,
                offset,
                -1 - buffer_index);
        }
    }
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_file_wrio_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "file_write on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_range_sync(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_, monad_async_file_offset offset, unsigned bytes,
    int flags)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    struct get_sqe_suspending_if_necessary_flags const flags_ = {
        .is_cancellation_point = false,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_wrsqe_suspending_if_necessary(ex, task, flags_);
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    io_uring_prep_sync_file_range(
        sqe, (int)file->io_uring_file_index_write, bytes, offset, flags);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_file_wrio_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "range_sync on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_file_durable_sync(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_file file_)
{
    struct monad_async_file_impl *file = (struct monad_async_file_impl *)file_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    struct get_sqe_suspending_if_necessary_flags const flags = {
        .is_cancellation_point = false,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_wrsqe_suspending_if_necessary(ex, task, flags);
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    io_uring_prep_fsync(sqe, (int)file->io_uring_file_index_write, 0);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_file_wrio_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_FILE_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "durable_sync on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}
