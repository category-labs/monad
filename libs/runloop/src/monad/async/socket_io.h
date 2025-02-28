#pragma once

#include "task.h"

#include <liburing.h>
#include <sys/socket.h>

#ifdef __cplusplus
extern "C"
{
#endif

//! \brief The public attributes of an open socket
typedef struct monad_async_socket_head
{
    // Either the locally bound or peer of connected socket
    MONAD_CONTEXT_PUBLIC_CONST struct sockaddr addr;
    MONAD_CONTEXT_PUBLIC_CONST socklen_t addr_len;

    // The following are not user modifiable
    struct monad_async_executor_head *MONAD_CONTEXT_PUBLIC_CONST executor;

    MONAD_CONTEXT_PUBLIC_CONST uint32_t total_io_submitted;
    MONAD_CONTEXT_PUBLIC_CONST uint32_t total_io_completed; // only in debug
} *monad_async_socket;

/*! \brief EXPENSIVE Create a socket. See `man socket` to explain parameters.

Note that `SO_LINGER` is set to zero to enable hard socket closes. If you want
different, create your own socket manually and add it to io_uring via
`monad_async_task_socket_create_from_existing_fd()`.

At least one malloc is performed, and possibly more.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_socket_create(
    monad_async_socket *sock, monad_async_task task, int domain, int type,
    int protocol, unsigned flags);

/*! \brief EXPENSIVE, CANCELLATION POINT Suspend execution of the task until the
userspace file descriptor has been registered with io_uring and a socket
instance representing it returned.

This function is provided purely for bridging this to legacy code -- wherever
possible you should use the native file and socket creation functions as
these completely bypass userspace and don't create any of the problems POSIX
file descriptors do.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_socket_create_from_existing_fd(
    monad_async_socket *sock, monad_async_task task, int fd);

//! \brief Suspend execution of the task until the socket has been closed
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_socket_destroy(monad_async_task task, monad_async_socket sock);

/*! \brief EXPENSIVE Bind a socket to an interface and port.

This is done by blocking syscall, as io_uring is currently incapable of doing
listening socket setup by itself.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_socket_bind(
    monad_async_socket sock, const struct sockaddr *addr, socklen_t addrlen);

/*! \brief EXPENSIVE Make a bound socket available for incoming connections.

This is done by blocking syscall, as io_uring is currently incapable of doing
listening socket setup by itself.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_socket_listen(monad_async_socket sock, int backlog);

/*! \brief CANCELLATION POINT Transfers the socket to io_uring, which may
require suspending the task.

As io_uring is currently incapable of doing listening socket setup by itself,
there is an explicit step for transferring the configured socket to io_uring
as it is an expensive operation.

Newer Linux kernels have an io_uring capable of connecting socket setup and
creation entirely within io_uring. If your kernel is so capable, that is used,
else blocking syscalls are used and the socket transferred into io_uring.

When this call returns, all syscall-created resources are released and io_uring
exclusively manages the socket.
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result
monad_async_task_socket_transfer_to_uring(
    monad_async_task task, monad_async_socket sock);

/*! \brief CANCELLATION POINT Suspend execution of the task if there is no
pending connection on the socket until there is a new connection. See `man
accept4` to explain parameters.

Note that `SO_LINGER` is set to zero to enable hard socket closes, which you
generally want as a server.

Note that if `SOCK_CLOEXEC` is set in the flags, io_uring will fail the request
(this is non-obvious, cost me half a day of debugging, so I document it here)
*/
BOOST_OUTCOME_C_NODISCARD extern monad_c_result monad_async_task_socket_accept(
    monad_async_socket *connected_sock, monad_async_task task,
    monad_async_socket listening_sock, int flags);

/*! \brief CANCELLATION POINT Initiate the connection of an open socket using
`iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man connect` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_socket_connect(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, const struct sockaddr *addr, socklen_t addrlen);

/*! \brief CANCELLATION POINT Initiate a shutdown of an open socket using
`iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man shutdown` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_socket_shutdown(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, int how);

/*! \brief CANCELLATION POINT Initiate a kernel allocated buffer read from an
open socket using `iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man recvmsg` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

If the executor was so configured, this API has io_uring allocate the buffer
which is more efficient than the application saying which buffer to fill. Upon
completion, `tofill->iovecs[0]` will be the buffer filled with up to `max_bytes`
(though it can be less). When you are done with the buffer, release it back to
io_uring using `monad_async_task_release_registered_io_buffer()`.
If this operation gets a result failure comparing equivalent to `ENOBUFS`,
then io_uring ran out of buffers to allocate. You should increase
`small_kernel_allocated_count` et al in `struct monad_async_executor_attr`.

If the executor was not configured with `small_kernel_allocated_count` et al,
then lack of i/o buffers will cause suspension of the calling task until i/o
buffers are released. You must still release buffers filled back to
io_uring using `monad_async_task_release_registered_io_buffer()`. You can still
receive a result failure comparing equivalent to `ENOBUFS` if the executor
would hang otherwise.

`max_bytes` chooses whether to use large or small page sized buffers and the
actual bytes read does not affect the size of buffer chosen.

\warning io_uring **requires** that the contents of `tofill` and everything it
points at have lifetime until the read completes.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_socket_receive(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock,
    struct monad_async_task_registered_io_buffer *tofill, size_t max_bytes,
    unsigned flags);

/*! \brief CANCELLATION POINT Initiate a scatter read from an open socket using
`iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man recvmsg` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of `msg` and everything it
points at have lifetime until the read completes.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_socket_receivev(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, struct msghdr *msg, unsigned flags);

/*! \brief CANCELLATION POINT Initiate a write to an open socket using
`iostatus` as the identifier.

Returns immediately unless there are no free io_uring submission entries.
See `man sendmsg` to explain parameters. The i/o priority used will be that
from the task's current i/o priority setting.

\warning io_uring **requires** that the contents of `msg` and everything it
points at have lifetime until the write completes.

Cancellation, or any other error, is reflected by the i/o status becoming
immediately completed with the error.
*/
extern void monad_async_task_socket_send(
    monad_async_io_status *iostatus, monad_async_task task,
    monad_async_socket sock, int buffer_index, const struct msghdr *msg,
    unsigned flags);

#ifdef __cplusplus
}
#endif
