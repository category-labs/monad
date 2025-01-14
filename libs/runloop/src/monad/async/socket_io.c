#include "socket_io.h"

#include "executor.h"

// #define MONAD_ASYNC_SOCKET_IO_PRINTING 1

#include "executor_impl.h"
#include "task_impl.h"

#include <errno.h>

#if !defined(IO_URING_VERSION_MAJOR)
static inline void io_uring_prep_socket_direct(
    struct io_uring_sqe *sqe, int domain, int type, int protocol,
    unsigned file_index, unsigned int flags)
{
    io_uring_prep_rw(
        45 /*IORING_OP_SOCKET*/,
        sqe,
        domain,
        NULL,
        (unsigned)protocol,
        (unsigned long long)type);
    sqe->rw_flags = (int)flags;
    __io_uring_set_target_fixed_file(sqe, file_index);
}
#endif

enum monad_async_socket_status : uint8_t
{
    monad_async_socket_status_not_created,
    monad_async_socket_status_userspace_file_descriptor,
    monad_async_socket_status_io_uring_file_index
};

struct monad_async_socket_impl
{
    struct monad_async_socket_head head;
    char magic[8];

    union
    {
        struct
        {
            int domain;
            int type;
            int protocol;
            unsigned flags;
        } not_created;

        int fd; // exists until moved into io_uring
    };

    enum monad_async_socket_status status;
    unsigned io_uring_file_index; // NOT a traditional file descriptor!
};

monad_c_result monad_async_task_socket_create(
    monad_async_socket *sock, monad_async_task task, int domain, int type,
    int protocol, unsigned flags)
{
    struct monad_async_socket_impl *p =
        (struct monad_async_socket_impl *)calloc(
            1, sizeof(struct monad_async_socket_impl));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->head.executor = task->current_executor;
    p->not_created.domain = domain;
    p->not_created.type = type;
    p->not_created.protocol = protocol;
    p->not_created.flags = flags;
    p->status = monad_async_socket_status_not_created;
    p->io_uring_file_index = (unsigned)-1;
    memcpy(p->magic, "MNASSOCK", 8);
    *sock = (monad_async_socket)p;
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_socket_create_from_existing_fd(
    monad_async_socket *sock, monad_async_task task_, int fd)
{
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    struct monad_async_socket_impl *p =
        (struct monad_async_socket_impl *)calloc(
            1, sizeof(struct monad_async_socket_impl));
    if (p == nullptr) {
        return monad_c_make_failure(errno);
    }
    p->head.executor = &ex->head;
    p->io_uring_file_index = (unsigned)-1;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        (void)monad_async_task_socket_destroy(task_, (monad_async_socket)p);
        return monad_c_make_failure(ECANCELED);
    }
    unsigned file_index = monad_async_executor_alloc_file_index(ex, fd);
    if (file_index == (unsigned)-1) {
        (void)monad_async_task_socket_destroy(task_, (monad_async_socket)p);
        return monad_c_make_failure(ENOMEM);
    }
    p->status = monad_async_socket_status_io_uring_file_index;
    p->io_uring_file_index = file_index;
    memcpy(p->magic, "MNASSOCK", 8);
    *sock = (monad_async_socket)p;
    return monad_c_make_success(0);
}

static monad_c_result monad_async_task_socket_destroy_impl(
    struct monad_async_task_impl *task, struct monad_async_socket_impl *sock)
{
    if (sock->io_uring_file_index != (unsigned)-1) {
        struct monad_async_executor_impl *ex =
            (struct monad_async_executor_impl *)atomic_load_explicit(
                &task->head.current_executor, memory_order_acquire);
        if (ex == nullptr) {
            return monad_c_make_failure(EINVAL);
        }
        struct get_sqe_suspending_if_necessary_flags const flags = {
            .is_cancellation_point = false,
            .max_concurrent_io_pacing_already_done = false};
        struct io_uring_sqe *sqe =
            get_sqe_suspending_if_necessary(ex, task, flags);
        io_uring_prep_close(sqe, 0);
        __io_uring_set_target_fixed_file(sqe, sock->io_uring_file_index);
        io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p initiates "
            "socket_close\n",
            (void *)task,
            (void *)ex);
        fflush(stdout);
#endif
        atomic_store_explicit(
            &task->head.is_suspended_for_io, true, memory_order_release);
        monad_c_result ret = monad_async_executor_suspend_impl(
            ex, task, nullptr, nullptr, nullptr);
        assert(
            atomic_load_explicit(
                &task->head.is_suspended_for_io, memory_order_acquire) == true);
        atomic_store_explicit(
            &task->head.is_suspended_for_io, false, memory_order_release);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p completes "
            "socket_close for file_index=%u and ret=%s\n",
            (void *)task,
            (void *)ex,
            sock->io_uring_file_index,
            BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)
                ? outcome_status_code_message(&ret.error)
                : "success");
        fflush(stdout);
#endif
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
            return ret;
        }
        monad_async_executor_free_file_index(ex, sock->io_uring_file_index);
    }
    memset(sock->magic, 0, 8);
    if (sock->status != monad_async_socket_status_userspace_file_descriptor) {
        close(sock->fd);
    }
    free(sock);
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_socket_destroy(
    monad_async_task task_, monad_async_socket sock_)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    // If socket close completes and the task has not been resumed yet,
    // cancelling the task will reset the result to cancelled thus turning this
    // non-cancellation point into a cancellation point. Detect this,
    // and sink the ECANCELED if it occurs.
    const enum monad_async_task_impl_please_cancel_invoked_status
        starting_please_cancel_status = task->please_cancel_status;
    monad_c_result ret = monad_async_task_socket_destroy_impl(
        task, (struct monad_async_socket_impl *)sock_);
    if (!BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        return ret;
    }
    if (task->please_cancel_status != starting_please_cancel_status &&
        outcome_status_code_equal_generic(&ret.error, ECANCELED)) {
        return monad_c_make_success(0);
    }
    return ret;
}

monad_c_result monad_async_task_socket_bind(
    monad_async_socket sock_, const struct sockaddr *addr, socklen_t addrlen)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    if (sock->status != monad_async_socket_status_not_created) {
        return monad_c_make_failure(EINVAL);
    }
    int fd = socket(
        sock->not_created.domain,
        sock->not_created.type,
        sock->not_created.protocol);
    if (fd < 0) {
        return monad_c_make_failure(errno);
    }
    if (bind(fd, addr, addrlen) < 0) {
        close(fd);
        return monad_c_make_failure(errno);
    }
    sock->head.addr_len = sizeof(sock->head.addr);
    if (getsockname(fd, &sock->head.addr, &sock->head.addr_len)) {
        close(fd);
        return monad_c_make_failure(errno);
    }
    sock->status = monad_async_socket_status_userspace_file_descriptor;
    sock->fd = fd;
    return monad_c_make_success(0);
}

monad_c_result
monad_async_task_socket_listen(monad_async_socket sock_, int backlog)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    if (sock->status != monad_async_socket_status_userspace_file_descriptor) {
        return monad_c_make_failure(EINVAL);
    }
    if (listen(sock->fd, backlog) < 0) {
        return monad_c_make_failure(errno);
    }
    return monad_c_make_success(0);
}

static inline monad_c_result monad_async_task_socket_task_op_cancel(
    struct monad_async_executor_impl *ex, struct monad_async_task_impl *task)
{
    struct io_uring_sqe *sqe = get_sqe_for_cancellation(ex);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(task), 0);
    sqe->user_data = (__u64)io_uring_mangle_into_data(task);
    return monad_c_make_failure(EAGAIN); // Canceller needs to wait
}

static inline monad_c_result monad_async_task_socket_iostatus_op_cancel(
    monad_async_task task_, monad_async_io_status *iostatus)
{
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task->head.current_executor, memory_order_acquire);
    struct io_uring_sqe *sqe = get_sqe_for_cancellation(ex);
    io_uring_prep_cancel(sqe, io_uring_mangle_into_data(iostatus), 0);
    sqe->user_data = (__u64)io_uring_mangle_into_data(iostatus);
    return monad_c_make_failure(EAGAIN); // Canceller needs to wait
}

monad_c_result monad_async_task_socket_transfer_to_uring(
    monad_async_task task_, monad_async_socket sock_)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    if (sock->status != monad_async_socket_status_not_created &&
        sock->status != monad_async_socket_status_userspace_file_descriptor) {
        return monad_c_make_failure(EINVAL);
    }
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        return monad_c_make_failure(ECANCELED);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    unsigned file_index = monad_async_executor_alloc_file_index(
        ex,
        (sock->status == monad_async_socket_status_userspace_file_descriptor)
            ? sock->fd
            : -1);
    if (file_index == (unsigned)-1) {
        (void)monad_async_task_socket_destroy(task_, sock_);
        return monad_c_make_failure(ENOMEM);
    }
    if (sock->status == monad_async_socket_status_not_created) {
        struct get_sqe_suspending_if_necessary_flags const flags = {
            .is_cancellation_point = true,
            .max_concurrent_io_pacing_already_done = false};
        struct io_uring_sqe *sqe =
            get_sqe_suspending_if_necessary(ex, task, flags);
        if (sqe == nullptr) {
            assert(task->please_cancel_status != please_cancel_not_invoked);
            (void)monad_async_task_socket_destroy(task_, sock_);
            return monad_c_make_failure(ECANCELED);
        }
        // This only works on newer Linux kernels, we have a fallback for older
        // kernels
        io_uring_prep_socket_direct(
            sqe,
            sock->not_created.domain,
            sock->not_created.type,
            sock->not_created.protocol,
            file_index,
            0);
        io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p initiates "
            "socket_create_direct\n",
            (void *)task,
            (void *)ex);
        fflush(stdout);
#endif
        atomic_store_explicit(
            &task->head.is_suspended_for_io, true, memory_order_release);
        monad_c_result ret = monad_async_executor_suspend_impl(
            ex, task, monad_async_task_socket_task_op_cancel, nullptr, nullptr);
        assert(
            atomic_load_explicit(
                &task->head.is_suspended_for_io, memory_order_acquire) == true);
        atomic_store_explicit(
            &task->head.is_suspended_for_io, false, memory_order_release);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p completes "
            "socket_create_direct with file_index=%u and ret=%s. If this "
            "failed, fallback will be used.\n",
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
            if (!outcome_status_code_equal_generic(&ret.error, EINVAL)) {
                (void)monad_async_task_socket_destroy(task_, sock_);
                return ret;
            }
            int fd = socket(
                sock->not_created.domain,
                sock->not_created.type,
                sock->not_created.protocol);
            if (fd < 0) {
                monad_c_result ret = monad_c_make_failure(errno);
                (void)monad_async_task_socket_destroy(task_, sock_);
                return ret;
            }
            file_index = monad_async_executor_alloc_file_index(ex, fd);
            close(fd);
            if (file_index == (unsigned)-1) {
                (void)monad_async_task_socket_destroy(task_, sock_);
                return monad_c_make_failure(ENOMEM);
            }
        }
    }
    else {
        // io_uring now owns this fd, so we can close it
        close(sock->fd);
        sock->fd = -1;
    }
    sock->status = monad_async_socket_status_io_uring_file_index;
    sock->io_uring_file_index = file_index;
    return monad_c_make_success(0);
}

monad_c_result monad_async_task_socket_accept(
    monad_async_socket *connected_sock_, monad_async_task task_,
    monad_async_socket sock_, int flags)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    if (sock->status != monad_async_socket_status_io_uring_file_index) {
        return monad_c_make_failure(EINVAL);
    }
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (task->please_cancel_status != please_cancel_not_invoked) {
        if (task->please_cancel_status < please_cancel_invoked_seen) {
            task->please_cancel_status = please_cancel_invoked_seen;
        }
        return monad_c_make_failure(ECANCELED);
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    if (ex == nullptr) {
        return monad_c_make_failure(EINVAL);
    }
    unsigned connected_file_index =
        monad_async_executor_alloc_file_index(ex, -1);
    if (connected_file_index == (unsigned)-1) {
        return monad_c_make_failure(ENOMEM);
    }
    struct get_sqe_suspending_if_necessary_flags const flags_ = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_sqe_suspending_if_necessary(ex, task, flags_);
    if (sqe == nullptr) {
        monad_async_executor_free_file_index(ex, connected_file_index);
        return monad_c_make_failure(ECANCELED);
    }
    struct sockaddr addr = {};
    socklen_t addr_len = sizeof(addr);
    io_uring_prep_accept_direct(
        sqe,
        (int)sock->io_uring_file_index,
        &addr,
        &addr_len,
        flags,
        connected_file_index);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, task, task, nullptr);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "socket_accept\n",
        (void *)task,
        (void *)ex);
    fflush(stdout);
#endif
    atomic_store_explicit(
        &task->head.is_suspended_for_io, true, memory_order_release);
    monad_c_result ret =
        monad_async_executor_suspend_impl(ex, task, nullptr, nullptr, nullptr);
    assert(
        atomic_load_explicit(
            &task->head.is_suspended_for_io, memory_order_acquire) == true);
    atomic_store_explicit(
        &task->head.is_suspended_for_io, false, memory_order_release);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
    printf(
        "*** Task %p running on executor %p completes "
        "socket_accept for file_index=%u and ret=%s\n",
        (void *)task,
        (void *)ex,
        connected_file_index,
        BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)
            ? outcome_status_code_message(&ret.error)
            : "success");
    fflush(stdout);
#endif
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        monad_async_executor_free_file_index(ex, connected_file_index);
        return ret;
    }
    ret = monad_async_task_socket_create(connected_sock_, task_, -1, 0, 0, 0);
    if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(ret)) {
        monad_async_executor_free_file_index(ex, connected_file_index);
        return ret;
    }
    struct monad_async_socket_impl *connected_sock =
        (struct monad_async_socket_impl *)*connected_sock_;
    memcpy(&connected_sock->head.addr, &addr, addr_len);
    connected_sock->head.addr_len = addr_len;
    connected_sock->status = monad_async_socket_status_io_uring_file_index;
    connected_sock->io_uring_file_index = connected_file_index;
    return monad_c_make_success(0);
}

void monad_async_task_socket_connect(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_socket sock_, const struct sockaddr *addr, socklen_t addrlen)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (sock->status != monad_async_socket_status_io_uring_file_index) {
        iostatus->result = monad_c_make_failure(EINVAL);
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    struct get_sqe_suspending_if_necessary_flags const flags = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task, flags);
    if (sqe == nullptr) {
        // Put straight onto completed i/o list
        iostatus->cancel_ = nullptr;
        iostatus->result = monad_c_make_failure(ECANCELED);
        iostatus->ticks_when_initiated = iostatus->ticks_when_completed =
            get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p fails to initiate "
            "socket_connect on i/o status %p due to cancellation\n",
            (void *)task,
            (void *)ex,
            (void *)iostatus);
        fflush(stdout);
#endif
        task = (struct monad_async_task_impl *)
                   task_->io_recipient_task; // WARNING: task may not be task!
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    io_uring_prep_connect(sqe, (int)sock->io_uring_file_index, addr, addrlen);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_socket_iostatus_op_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "socket_connect on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_socket_shutdown(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_socket sock_, int how)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (sock->status != monad_async_socket_status_io_uring_file_index) {
        iostatus->result = monad_c_make_failure(EINVAL);
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    struct get_sqe_suspending_if_necessary_flags const flags = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe = get_sqe_suspending_if_necessary(ex, task, flags);
    if (sqe == nullptr) {
        // Put straight onto completed i/o list
        iostatus->cancel_ = nullptr;
        iostatus->result = monad_c_make_failure(ECANCELED);
        iostatus->ticks_when_initiated = iostatus->ticks_when_completed =
            get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p fails to initiate "
            "socket_shutdown on i/o status %p due to cancellation\n",
            (void *)task,
            (void *)ex,
            (void *)iostatus);
        fflush(stdout);
#endif
        task = (struct monad_async_task_impl *)
                   task_->io_recipient_task; // WARNING: task may not be task!
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    io_uring_prep_shutdown(sqe, (int)sock->io_uring_file_index, how);
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_socket_iostatus_op_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "socket_shutdown on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_socket_receive(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_socket sock_,
    struct monad_async_task_registered_io_buffer *tofill, size_t max_bytes,
    unsigned flags)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (sock->status != monad_async_socket_status_io_uring_file_index) {
        iostatus->result = monad_c_make_failure(EINVAL);
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    assert(
        ex->registered_buffers[0].buffers !=
        nullptr); // use receivev() if you haven't set up buffers
    assert(
        tofill->iov[0].iov_base == nullptr); // io_uring allocates this for you!
    bool const is_large_page =
        (max_bytes > ex->registered_buffers[0].buffer[0].size);
    __u16 buffer_index = 0;
    if (ex->registered_buffers[0].buffer[is_large_page].buf_ring_count == 0) {
        const struct monad_async_task_claim_registered_io_buffer_flags flags_ =
            {.fail_dont_suspend = false, ._for_read_ring = true};
        monad_c_result r =
            monad_async_task_claim_registered_file_io_write_buffer(
                tofill, task_, max_bytes, flags_);
        if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
            assert(tofill->index == 0);
            // Put straight onto completed i/o list
            iostatus->cancel_ = nullptr;
            iostatus->result = r;
            iostatus->ticks_when_initiated = iostatus->ticks_when_completed =
                get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
            printf(
                "*** Task %p running on executor %p fails to initiate "
                "socket_recv on i/o status %p buffer_index=%d max_bytes=%zu "
                "due to %s\n",
                (void *)task,
                (void *)ex,
                (void *)iostatus,
                buffer_index,
                max_bytes,
                BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)
                    ? outcome_status_code_message(&r.error)
                    : "success");
            fflush(stdout);
#endif
            task =
                (struct monad_async_task_impl *)
                    task_->io_recipient_task; // WARNING: task may not be task!
            LIST_APPEND(
                task->io_completed,
                iostatus,
                &task->head.io_completed_not_reaped);
            return;
        }
        buffer_index = (__u16)tofill->index - 1;
    }
    else {
        buffer_index = is_large_page; // buffer group
    }
    struct get_sqe_suspending_if_necessary_flags const flags_ = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_sqe_suspending_if_necessary(ex, task, flags_);
    if (sqe == nullptr) {
        // Put straight onto completed i/o list
        iostatus->cancel_ = nullptr;
        iostatus->result = monad_c_make_failure(ECANCELED);
        iostatus->ticks_when_initiated = iostatus->ticks_when_completed =
            get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p fails to initiate "
            "socket_recv on i/o status %p due to cancellation\n",
            (void *)task,
            (void *)ex,
            (void *)iostatus);
        fflush(stdout);
#endif
        task = (struct monad_async_task_impl *)
                   task_->io_recipient_task; // WARNING: task may not be task!
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        if (tofill->index != 0) {
            MONAD_CHECK_RESULT(monad_async_task_release_registered_io_buffer(
                task_, tofill->index));
            memset(tofill, 0, sizeof(*tofill));
        }
        return;
    }
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    io_uring_prep_recv(
        sqe,
        (int)sock->io_uring_file_index,
        tofill->iov[0].iov_base,
        max_bytes,
        (int)flags);
    sqe->buf_index = buffer_index;
    sqe->flags |= IOSQE_FIXED_FILE;
    if (ex->registered_buffers[0].buffer[is_large_page].buf_ring_count > 0) {
        sqe->flags |= IOSQE_BUFFER_SELECT;
    }
    io_uring_sqe_set_data(sqe, iostatus, task, tofill);
    iostatus->cancel_ = monad_async_task_socket_iostatus_op_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "socket_recv on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_socket_receivev(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_socket sock_, struct msghdr *msg, unsigned flags)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (sock->status != monad_async_socket_status_io_uring_file_index) {
        iostatus->result = monad_c_make_failure(EINVAL);
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    struct get_sqe_suspending_if_necessary_flags const flags_ = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_sqe_suspending_if_necessary(ex, task, flags_);
    if (sqe == nullptr) {
        // Put straight onto completed i/o list
        iostatus->cancel_ = nullptr;
        iostatus->result = monad_c_make_failure(ECANCELED);
        iostatus->ticks_when_initiated = iostatus->ticks_when_completed =
            get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p fails to initiate "
            "socket_recv on i/o status %p due to cancellation\n",
            (void *)task,
            (void *)ex,
            (void *)iostatus);
        fflush(stdout);
#endif
        task = (struct monad_async_task_impl *)
                   task_->io_recipient_task; // WARNING: task may not be task!
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    if (msg->msg_iovlen != 1) {
        io_uring_prep_recvmsg(sqe, (int)sock->io_uring_file_index, msg, flags);
    }
    else {
        io_uring_prep_recv(
            sqe,
            (int)sock->io_uring_file_index,
            msg->msg_iov[0].iov_base,
            msg->msg_iov[0].iov_len,
            (int)flags);
    }
    int const buffer_index = infer_buffer_index_if_possible(
        ex, msg->msg_iov, msg->msg_iovlen, false);
    if (buffer_index != 0) {
        assert(buffer_index > 0);
        sqe->buf_index = (__u16)buffer_index - 1;
    }
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_socket_iostatus_op_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "socket_recv on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}

void monad_async_task_socket_send(
    monad_async_io_status *iostatus, monad_async_task task_,
    monad_async_socket sock_, int buffer_index, const struct msghdr *msg,
    unsigned flags)
{
    struct monad_async_socket_impl *sock =
        (struct monad_async_socket_impl *)sock_;
    struct monad_async_task_impl *task = (struct monad_async_task_impl *)task_;
    if (sock->status != monad_async_socket_status_io_uring_file_index) {
        iostatus->result = monad_c_make_failure(EINVAL);
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    struct monad_async_executor_impl *ex =
        (struct monad_async_executor_impl *)atomic_load_explicit(
            &task_->current_executor, memory_order_acquire);
    assert(ex != nullptr);
    // NOT get_wrsqe_suspending_if_necessary!
    struct get_sqe_suspending_if_necessary_flags const flags_ = {
        .is_cancellation_point = true,
        .max_concurrent_io_pacing_already_done = false};
    struct io_uring_sqe *sqe =
        get_sqe_suspending_if_necessary(ex, task, flags_);
    if (sqe == nullptr) {
        // Put straight onto completed i/o list
        iostatus->cancel_ = nullptr;
        iostatus->result = monad_c_make_failure(ECANCELED);
        iostatus->ticks_when_initiated = iostatus->ticks_when_completed =
            get_ticks_count(memory_order_relaxed);
#if MONAD_ASYNC_SOCKET_IO_PRINTING
        printf(
            "*** Task %p running on executor %p fails to initiate "
            "socket_send on i/o status %p due to cancellation\n",
            (void *)task,
            (void *)ex,
            (void *)iostatus);
        fflush(stdout);
#endif
        task = (struct monad_async_task_impl *)
                   task_->io_recipient_task; // WARNING: task may not be task!
        LIST_APPEND(
            task->io_completed, iostatus, &task->head.io_completed_not_reaped);
        return;
    }
    task = (struct monad_async_task_impl *)
               task_->io_recipient_task; // WARNING: task may not be task!
    if (msg->msg_iovlen != 1) {
        io_uring_prep_sendmsg(sqe, (int)sock->io_uring_file_index, msg, flags);
    }
    else {
        io_uring_prep_send(
            sqe,
            (int)sock->io_uring_file_index,
            msg->msg_iov[0].iov_base,
            msg->msg_iov[0].iov_len,
            (int)flags);
    }
    if (buffer_index == 0) {
        buffer_index = infer_buffer_index_if_possible(
            ex, msg->msg_iov, msg->msg_iovlen, true);
    }
    if (buffer_index != 0) {
        assert(buffer_index > 0);
        sqe->buf_index = (__u16)buffer_index - 1;
    }
    sqe->flags |= IOSQE_FIXED_FILE;
    io_uring_sqe_set_data(sqe, iostatus, task, nullptr);
    iostatus->cancel_ = monad_async_task_socket_iostatus_op_cancel;
    iostatus->ticks_when_initiated = get_ticks_count(memory_order_relaxed);

#if MONAD_ASYNC_SOCKET_IO_PRINTING
    printf(
        "*** Task %p running on executor %p initiates "
        "socket_send on i/o status %p\n",
        (void *)task,
        (void *)ex,
        (void *)iostatus);
    fflush(stdout);
#endif
    LIST_APPEND(task->io_submitted, iostatus, &task->head.io_submitted);
}
