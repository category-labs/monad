#pragma once

#include "task.h"

#include <liburing.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief An offset into a file
typedef uint64_t monad_async_file_offset;

//! \brief The public attributes of an open file
typedef struct monad_async_file_head
{
    // The following are not user modifiable
    struct monad_async_executor_head *MONAD_CONTEXT_PUBLIC_CONST executor;
} *monad_async_file;

/*! \brief EXPENSIVE, CANCELLATION POINT Suspend execution of the task until the
file has been opened. See `man open2` to explain parameters.

This is a relatively expensive operation as it may do up to two mallocs and
several syscalls per call.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_file_create(
    monad_async_file *file, monad_async_task task, monad_async_file base,
    char const *subpath, struct open_how *how);

/*! \brief EXPENSIVE, CANCELLATION POINT Suspend execution of the task until the
userspace file descriptor has been registered with io_uring and a file instance
representing it returned.

This function is provided purely for bridging this to legacy code -- wherever
possible you should use the native file and socket creation functions as
these completely bypass userspace and don't create any of the problems POSIX
file descriptors do.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_file_create_from_existing_fd(
    monad_async_file *file, monad_async_task task, int fd);

//! \brief Suspend execution of the task until the file has been closed
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_file_destroy(monad_async_task task, monad_async_file file);

//! \brief CANCELLATION POINT Suspend execution of the task until the file's
//! valid extents have been modified as per the `fallocate` call, see `man
//! fallocate` for more.
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_file_fallocate(
    monad_async_task task, monad_async_file file, int mode,
    monad_async_file_offset offset, monad_async_file_offset len);

/*! \brief CANCELLATION POINT Initiate a ring buffer read from an open file
using `iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man readv2` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

Upon completion, `tofill->iovecs[0]` will be the buffer filled with up to
`max_bytes` (though it can be less). When you are done with the buffer, release
it back to io_uring using `monad_async_task_release_registered_io_buffer()`.
Lack of i/o buffers will cause suspension of the calling task until i/o
buffers are released. If the lack of i/o buffers across all tasks would cause
deadlock, it is possible for an i/o to complete with failure comparing
equivalent to `ENOBUFS`, in which case you should retry the operation.

`max_bytes` chooses whether to use large or small page sized buffers and the
actual bytes read does not affect the size of buffer chosen.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_file_read(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file, struct monad_async_task_registered_io_buffer *tofill,
    size_t max_bytes, monad_async_file_offset offset, int flags);

/*! \brief CANCELLATION POINT Initiate a scatter read from an open file using
`iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man readv2` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of iovecs have lifetime until
the read completes. The only exception here is if `nr_vecs` is one.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_file_readv(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file, const struct iovec *iovecs, unsigned nr_vecs,
    monad_async_file_offset offset, int flags);

/*! \brief CANCELLATION POINT Initiate a write to an open file using `iostatus`
as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man writev2` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of iovecs have lifetime until
the writes completes. The only exception here is if `nr_vecs` is one.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_file_write(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file, int buffer_index, const struct iovec *iovecs,
    unsigned nr_vecs, monad_async_file_offset offset, int flags);

//! \brief CANCELLATION POINT Initiate a flush of dirty file extents using
//! `iostatus` as the identifier. Returns immediately unless there are no free
//! io_uring submission entries. See `man sync_file_range` to explain
//! parameters. The i/o priority used will be that from the task's current i/o
//! priority setting. This is the right call to use to encourage the kernel to
//! flush a region of data now, it is the wrong call to ensure write durability
//! as it neither flushes metadata nor tells the storage device to flush.
extern void monad_async_task_file_range_sync(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file, monad_async_file_offset offset, unsigned bytes,
    int flags);

//! \brief CANCELLATION POINT Initiate a durable sync of an open file using
//! `iostatus` as the identifier. Returns immediately unless there are no free
//! io_uring submission entries. The i/o priority used will be that from the
//! task's current i/o priority setting. This is the right call to use to ensure
//! written data is durably placed onto non-volatile storage.
//!
//! Note that this operation generally takes milliseconds to complete.
extern void monad_async_task_file_durable_sync(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_file file);

#ifdef __cplusplus
}
#endif
