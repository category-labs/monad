#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbit.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <poll.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>

#include <monad/event/event.h>
#include <monad/event/event_client.h>

#include <monad/event/event_iterator.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>

union server_response
{
    enum monad_event_msg_type msg_type;
    struct monad_event_export_error_msg err_msg;
    struct monad_event_export_success_msg ok_msg;
};

static thread_local char error_buf[1024];

__attribute__((format(printf, 2, 3))) static int
format_errc(int err, char const *format, ...)
{
    int len;
    va_list ap;

    va_start(ap, format);
    len = vsnprintf(error_buf, sizeof error_buf, format, ap);
    va_end(ap);
    if ((size_t)len < sizeof error_buf) {
        snprintf(
            error_buf + len,
            sizeof error_buf - (size_t)len,
            ": %s (%d)",
            strerror(err),
            err);
    }
    return err;
}

static void add_connect_option_defaults(
    struct monad_event_connect_options const *user_opts,
    struct monad_event_connect_options *opts)
{
    *opts = *user_opts;
    if (opts->socket_path == nullptr || *opts->socket_path == '\0') {
        opts->socket_path = MONAD_EVENT_DEFAULT_SOCKET_PATH;
    }
}

static int
map_ring_control(struct monad_event_ring *ring, struct msghdr const *mhdr)
{
    int control_fd;
    int saved_error;
    struct monad_event_export_success_msg *msg;
    struct cmsghdr const *cmsg = CMSG_FIRSTHDR(mhdr);
    if (cmsg == nullptr || cmsg->cmsg_level != SOL_SOCKET ||
        cmsg->cmsg_type != SCM_RIGHTS) {
        return format_errc(
            EPROTO,
            "expected MAP_RING_CONTROL message to carry "
            "a memfd descriptor");
    }
    msg = mhdr->msg_iov[0].iov_base;
    ring->capacity = msg->ring_capacity;
    control_fd = *(int *)CMSG_DATA(cmsg);
    ring->control = mmap(
        nullptr, (size_t)getpagesize(), PROT_READ, MAP_SHARED, control_fd, 0);
    if (ring->control == MAP_FAILED) {
        saved_error = format_errc(
            errno, "unable to map ring control segment into process");
        goto Done;
    }
    saved_error = 0;

Done:
    (void)close(control_fd);
    return saved_error;
}

static int
map_descriptor_table(struct monad_event_ring *ring, struct msghdr const *mhdr)
{
    int saved_error;
    int descriptor_table_fd;
    struct cmsghdr const *cmsg = CMSG_FIRSTHDR(mhdr);
    struct monad_event_export_success_msg const *const msg =
        mhdr->msg_iov[0].iov_base;
    size_t const desc_table_map_len =
        msg->ring_capacity * sizeof(struct monad_event_descriptor);
    if (cmsg == nullptr || cmsg->cmsg_level != SOL_SOCKET ||
        cmsg->cmsg_type != SCM_RIGHTS) {
        return format_errc(
            EPROTO,
            "expected MAP_DESCRIPTOR_TABLE message to "
            "carry a memfd descriptor");
    }
    descriptor_table_fd = *(int *)CMSG_DATA(cmsg);
    ring->descriptor_table = mmap(
        nullptr,
        desc_table_map_len,
        PROT_READ,
        MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
        descriptor_table_fd,
        0);
    if (ring->descriptor_table == MAP_FAILED) {
        saved_error = format_errc(errno, "unable to map ring descriptor table");
        goto Done;
    }
    saved_error = 0;

Done:
    (void)close(descriptor_table_fd);
    return saved_error;
}

static int
map_payload_buffer(struct monad_event_ring *ring, struct msghdr const *mhdr)
{
    int saved_error;
    int payload_buf_fd;
    struct stat memfd_stat;
    struct cmsghdr const *cmsg = CMSG_FIRSTHDR(mhdr);
    if (cmsg == nullptr || cmsg->cmsg_level != SOL_SOCKET ||
        cmsg->cmsg_type != SCM_RIGHTS) {
        return format_errc(
            EPROTO,
            "expected MAP_PAYLOAD_BUFFER message to "
            "carry a memfd descriptor");
    }
    payload_buf_fd = *(int *)CMSG_DATA(cmsg);
    if (fstat(payload_buf_fd, &memfd_stat) == -1) {
        saved_error = format_errc(errno, "fstat(2) of payload buffer failed");
        (void)close(payload_buf_fd);
        return saved_error;
    }
    ring->payload_buf_size = (size_t)memfd_stat.st_size;
    assert(
        stdc_has_single_bit(ring->payload_buf_size) &&
        stdc_has_single_bit(MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE));
    ring->payload_buf = mmap(
        nullptr,
        ring->payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
        PROT_READ,
        MAP_ANONYMOUS | MAP_SHARED | MAP_HUGETLB,
        -1,
        0);
    if (ring->payload_buf == MAP_FAILED) {
        saved_error = format_errc(
            errno, "mmap(2) unable to reserve payload buffer VM region");
        goto Done;
    }
    if (mmap(
            ring->payload_buf,
            ring->payload_buf_size,
            PROT_READ,
            MAP_FIXED | MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
            payload_buf_fd,
            0) == MAP_FAILED) {
        saved_error = format_errc(errno, "unable to remap payload buffer");
        goto Done;
    }
    if (mmap(
            (uint8_t *)ring->payload_buf + ring->payload_buf_size,
            MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE,
            PROT_READ,
            MAP_FIXED | MAP_SHARED | MAP_HUGETLB,
            payload_buf_fd,
            0) == MAP_FAILED) {
        saved_error = format_errc(
            errno, "unable to remap wrap-around ring descriptor page");
        goto Done;
    }
    saved_error = 0;

Done:
    (void)close(payload_buf_fd);
    return saved_error;
}

static int map_metadata_page(
    void const **page_p, size_t *page_len, struct msghdr const *mhdr)
{
    int memfd;
    struct stat memfd_stat;
    int saved_error;
    struct cmsghdr const *cmsg = CMSG_FIRSTHDR(mhdr);

    if (cmsg == nullptr || cmsg->cmsg_level != SOL_SOCKET ||
        cmsg->cmsg_type != SCM_RIGHTS) {
        return format_errc(
            EPROTO,
            "expected MAP_METADATA_PAGE message to "
            "carry a memfd descriptor");
    }
    memfd = *(int *)CMSG_DATA(cmsg);
    if (fstat(memfd, &memfd_stat) == -1) {
        saved_error = format_errc(errno, "fstat(2) of metadata page failed");
        (void)close(memfd);
        return saved_error;
    }
    *page_len = (size_t)memfd_stat.st_size;
    *page_p = mmap(
        nullptr,
        *page_len,
        PROT_READ,
        MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
        memfd,
        0);
    if (*page_p == MAP_FAILED) {
        saved_error = format_errc(errno, "unable to map metadata page");
        (void)close(memfd);
        *page_p = nullptr;
        return saved_error;
    }
    (void)close(memfd);
    return 0;
}

static int set_metadata_table(
    struct monad_event_export_success_msg const *msg,
    struct monad_event_proc *proc, void const **table)
{
    if (table == nullptr) {
        return 0;
    }
    if (proc->metadata_page == nullptr) {
        return format_errc(
            EPROTO,
            "saw METADATA_OFFSET message before "
            "expected metadata page");
    }
    if (proc->metadata_page_len <= msg->metadata_offset) {
        return format_errc(
            EPROTO,
            "protocol advertised out-of-bounds offset on metadata page");
    }
    switch (msg->metadata_type) {
    case MONAD_EVENT_METADATA_THREAD:
        [[fallthrough]];
    case MONAD_EVENT_METADATA_BLOCK_FLOW:
        *table = (uint8_t const *)proc->metadata_page + msg->metadata_offset;
        return 0;
    default:
        return format_errc(
            EPROTO, "unknown metadata map type %hhu", msg->metadata_type);
    }
}

static int recv_metadata_msgs(struct monad_event_proc *proc)
{
    int rc;
    union server_response response;

    union
    {
        char buf[CMSG_LEN(sizeof(int))];
        struct cmsghdr hdr;
    } cmsg;
    struct iovec msg_iov[1] = {
        [0] = {.iov_base = &response, .iov_len = sizeof response}};
    struct msghdr mhdr = {
        .msg_name = nullptr,
        .msg_namelen = 0,
        .msg_iov = msg_iov,
        .msg_iovlen = 1,
        .msg_control = cmsg.buf,
        .msg_controllen = sizeof cmsg};

    // As soon we connect, the server will immediately push these metadata
    // messages to us:
    //
    //   MONAD_EVENT_MSG_MAP_METADATA_PAGE - file descriptor of the metadata
    //       page (there should only be one of these)
    //
    //   MONAD_EVENT_MSG_METADATA_OFFSET - explains where in the metadata
    //       page one of the metadata arrays is located; the
    //       MONAD_EVENT_MSG_MAP_METADATA_PAGE for that page will already have
    //       been received
    //
    //   MONAD_EVENT_MSG_EXPORT_FINISHED - if this message is seen, the
    //       connection process completed successfully
    //
    //   MONAD_EVENT_MSG_EXPORT_ERROR - if this message is seen, the connection
    //       process has failed, and no more messages will be sent

    response.msg_type = MONAD_EVENT_MSG_NONE;
    while (response.msg_type != MONAD_EVENT_MSG_EXPORT_FINISHED) {
        if (recvmsg(proc->sock_fd, &mhdr, 0) == -1) {
            return format_errc(errno, "recvmsg(2) from event server failed");
        }

        switch (response.msg_type) {
        case MONAD_EVENT_MSG_EXPORT_ERROR:
            rc = response.err_msg.error_code != 0 ? response.err_msg.error_code
                                                  : EIO;
            return format_errc(
                rc,
                "event server reported error: %s",
                response.err_msg.error_buf);

        case MONAD_EVENT_MSG_MAP_METADATA_PAGE:
            if (proc->metadata_page != nullptr) {
                return format_errc(EPROTO, "metadata page mapped twice");
            }
            if ((rc = map_metadata_page(
                     &proc->metadata_page, &proc->metadata_page_len, &mhdr)) !=
                0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_METADATA_OFFSET:
            if ((rc = set_metadata_table(
                     &response.ok_msg,
                     proc,
                     response.ok_msg.metadata_type ==
                             MONAD_EVENT_METADATA_THREAD
                         ? (void const **)&proc->thread_table
                         : (void const **)&proc->block_header_table)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_EXPORT_FINISHED:
            return 0;

        default:
            return format_errc(
                EPROTO,
                "unexpected msg type %u from "
                "event server during connect",
                response.msg_type);
        }
    }

    return 0;
}

static int import_ring(struct monad_event_imported_ring *import)
{
    int rc;
    union server_response response;

    union
    {
        char buf[CMSG_LEN(sizeof(int))];
        struct cmsghdr hdr;
    } cmsg;
    struct iovec msg_iov[1] = {
        [0] = {.iov_base = &response, .iov_len = sizeof response}};
    struct msghdr mhdr = {
        .msg_name = nullptr,
        .msg_namelen = 0,
        .msg_iov = msg_iov,
        .msg_iovlen = 1,
        .msg_control = cmsg.buf,
        .msg_controllen = sizeof cmsg};
    struct monad_event_export_ring_msg open_msg = {
        .msg_type = MONAD_EVENT_MSG_EXPORT_RING, .ring_type = import->type};
    memcpy(
        open_msg.event_metadata_hash,
        g_monad_event_metadata_hash,
        sizeof open_msg.event_metadata_hash);

    // The process of importing an event ring is:
    //
    //   1. We send a MONAD_EVENT_MSG_EXPORT_RING message to the server
    //
    //   2. The server sends several messages in response. Most of the
    //      response messages describe a single shared memory segment and bear
    //      a memfd_create(2) file descriptor as ancillary cmsg data.
    //
    // The message types sent in response are:
    //
    //   MONAD_EVENT_MSG_MAP_RING_CONTROL - file descriptor of the event ring
    //       control page segment
    //
    //   MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE - file descriptor of the event
    //       descriptor table
    //
    //   MONAD_EVENT_MSG_MAP_PAYLOAD_BUFFER - file descriptor of the payload
    //       buffer
    //
    //   MONAD_EVENT_MSG_EXPORT_FINISHED - if this message is seen, the import
    //       process completed successfully
    //
    //   MONAD_EVENT_MSG_EXPORT_ERROR - if this message is seen, the importing
    //       process has failed, and no more messages will be sent

    if (send(import->proc->sock_fd, &open_msg, sizeof open_msg, 0) !=
        sizeof open_msg) {
        return format_errc(errno, "send(2) of EXPORT_RING message failed");
    }
    response.msg_type = MONAD_EVENT_MSG_NONE;
    while (response.msg_type != MONAD_EVENT_MSG_EXPORT_FINISHED) {
        if (recvmsg(import->proc->sock_fd, &mhdr, 0) == -1) {
            return format_errc(errno, "recvmsg(2) from event server failed");
        }

        switch (response.msg_type) {
        case MONAD_EVENT_MSG_EXPORT_ERROR:
            rc = response.err_msg.error_code != 0 ? response.err_msg.error_code
                                                  : EIO;
            return format_errc(
                rc,
                "event server reported error: %s",
                response.err_msg.error_buf);

        case MONAD_EVENT_MSG_MAP_RING_CONTROL:
            if ((rc = map_ring_control(&import->ring, &mhdr)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE:
            if ((rc = map_descriptor_table(&import->ring, &mhdr)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_MAP_PAYLOAD_BUFFER:
            if ((rc = map_payload_buffer(&import->ring, &mhdr)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_EXPORT_FINISHED:
            return 0;

        default:
            return format_errc(
                EPROTO,
                "unexpected msg type %u from "
                "event server",
                response.msg_type);
        }
    }

    return 0;
}

/*
 * Bitmap allocation stuff. We set a maximum number of monad_event_proc and
 * monad_event_imported_ring structures and allocate them using a presence
 * bitmap. There will likely never be more than 1 or 2 of these objects, and
 * doing it this way makes it easy to detect double-frees, use-after-free,
 * or bad pointers.
 */

struct monad_event_proc s_procs[MONAD_EVENT_PROC_MAX];
struct monad_event_proc const *const s_procs_end =
    s_procs + MONAD_EVENT_PROC_MAX;

struct monad_event_imported_ring s_imports[MONAD_EVENT_IMPORTED_RING_MAX];
struct monad_event_imported_ring const *const s_imports_end =
    s_imports + MONAD_EVENT_IMPORTED_RING_MAX;

static atomic_uint s_proc_bitmap;
static atomic_uint s_import_bitmap;

static_assert(sizeof s_proc_bitmap == MONAD_EVENT_PROC_MAX / CHAR_BIT);
static_assert(
    sizeof s_import_bitmap == MONAD_EVENT_IMPORTED_RING_MAX / CHAR_BIT);

static bool try_alloc_bit(atomic_uint *bitmap, unsigned *bit)
{
    unsigned cur_bits = atomic_load_explicit(bitmap, memory_order_relaxed);
    unsigned alloc_bits;
TryAgain:
    *bit = stdc_first_trailing_zero(cur_bits);
    if (*bit == 0) {
        return false;
    }
    alloc_bits = cur_bits | (1U << (*bit - 1));
    if (!atomic_compare_exchange_weak_explicit(
            bitmap,
            &cur_bits,
            alloc_bits,
            memory_order_acq_rel,
            memory_order_acquire)) {
        goto TryAgain;
    }
    return true;
}

static void free_bit(atomic_uint *bitmap, unsigned bit)
{
    unsigned mask = 1U << (bit - 1);
    unsigned cur_bits = atomic_load_explicit(bitmap, memory_order_relaxed);
    unsigned dealloc_bits;

    assert(cur_bits & mask);
TryAgain:
    dealloc_bits = cur_bits & ~mask;
    if (!atomic_compare_exchange_weak_explicit(
            bitmap,
            &cur_bits,
            dealloc_bits,
            memory_order_acq_rel,
            memory_order_acquire)) {
        goto TryAgain;
    }
}

static void cleanup_proc(struct monad_event_proc *proc)
{
    assert(TAILQ_EMPTY(&proc->imports));
    pthread_mutex_destroy(&proc->mtx);
    if (proc->metadata_page != nullptr) {
        munmap((void *)proc->metadata_page, proc->metadata_page_len);
    }
    free_bit(&s_proc_bitmap, (unsigned)(proc - s_procs + 1));
}

static void cleanup_imported_ring(struct monad_event_imported_ring *import)
{
    struct monad_event_proc *const proc = import->proc;
    struct monad_event_ring *const ring = &import->ring;

    pthread_mutex_lock(&proc->mtx);
    TAILQ_REMOVE(&proc->imports, import, next);
    pthread_mutex_unlock(&proc->mtx);
    if (atomic_fetch_sub_explicit(&proc->refcount, 1, memory_order_acq_rel) ==
        1) {
        cleanup_proc(proc);
    }

    // Unmap the event ring segments
    if (ring->control != nullptr) {
        munmap(ring->control, (size_t)getpagesize());
    }
    if (ring->descriptor_table != nullptr) {
        size_t const map_len =
            ring->capacity * sizeof(struct monad_event_descriptor);
        munmap(ring->descriptor_table, map_len);
    }
    if (ring->payload_buf != nullptr) {
        munmap(
            ring->payload_buf,
            ring->payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE);
    }

    free_bit(&s_import_bitmap, (unsigned)(import - s_imports + 1));
}

int monad_event_proc_connect(
    struct monad_event_connect_options const *user_opts,
    struct monad_event_proc **proc_p)
{
    int saved_error;
    struct sockaddr_un server_addr;
    struct monad_event_proc *proc;
    struct monad_event_connect_options opts;
    unsigned alloc_bit;

    if (proc_p == nullptr) {
        return format_errc(EINVAL, "proc_p cannot be nullptr");
    }
    *proc_p = nullptr;

    if (user_opts == nullptr) {
        return format_errc(EINVAL, "user_opts cannot be nullptr");
    }
    // Even when the options are explicitly supplied, some values may have a
    // "use default" sentinel value (e.g., 0) that needs to be replaced
    add_connect_option_defaults(user_opts, &opts);
    if (!try_alloc_bit(&s_proc_bitmap, &alloc_bit)) {
        return format_errc(ENOBUFS, "no free monad_proc structures available");
    }
    proc = &s_procs[alloc_bit - 1];
    memset(proc, 0, sizeof *proc);
    if ((saved_error = pthread_mutex_init(&proc->mtx, nullptr)) != 0) {
        free_bit(&s_proc_bitmap, alloc_bit);
        return format_errc(saved_error, "pthread_mutex_init failed");
    }
    atomic_store_explicit(&proc->refcount, 1, memory_order_release);
    // Set to -1 in case we cleanup early (so we don't accidentally close fd 0)
    proc->sock_fd = -1;
    TAILQ_INIT(&proc->imports);

    // Copy the path to the UNIX domain socket
    server_addr.sun_family = AF_LOCAL;
    if (strlcpy(
            server_addr.sun_path,
            opts.socket_path,
            sizeof server_addr.sun_path) >= sizeof server_addr.sun_path) {
        saved_error = format_errc(
            ENAMETOOLONG,
            "socket path `%s` exceeds maximum "
            "length %lu",
            opts.socket_path,
            sizeof server_addr.sun_path);
        goto Cleanup;
    }

    // Create a blocking socket with the requested receive timeout and connect
    // to the event server
    proc->sock_fd = socket(PF_LOCAL, SOCK_SEQPACKET, 0);
    if (proc->sock_fd == -1) {
        saved_error = format_errc(errno, "socket(2) failed");
        goto Cleanup;
    }
    if ((opts.socket_timeout.tv_sec != 0 || opts.socket_timeout.tv_usec != 0) &&
        setsockopt(
            proc->sock_fd,
            SOL_SOCKET,
            SO_RCVTIMEO,
            &opts.socket_timeout,
            sizeof opts.socket_timeout) == -1) {
        saved_error =
            format_errc(errno, "unable to set SO_RCVTIMEO for client socket");
        goto Cleanup;
    }
    if (connect(
            proc->sock_fd,
            (struct sockaddr const *)&server_addr,
            sizeof server_addr) == -1) {
        saved_error = format_errc(
            errno,
            "unable to connect to event server socket endpoint `%s`",
            server_addr.sun_path);
        goto Cleanup;
    }

    // Upon a successful connection, the server will immediately push the
    // metadata messages to us.
    if ((saved_error = recv_metadata_msgs(proc)) != 0) {
        goto Cleanup;
    }
    *proc_p = proc;
    return 0;

Cleanup:
    if (monad_event_proc_disconnect(proc) == ENOTCONN) {
        // It failed early enough that it didn't need to disconnect. In this
        // case, it assumes this is a "double-free" error and returns ENOTCONN
        // rather than modifying the reference count. We need to destroy it
        // manually.
        cleanup_proc(proc);
    }
    return saved_error;
}

int monad_event_proc_disconnect(struct monad_event_proc *proc)
{
    int old_fd;

    if (proc < s_procs || proc > s_procs_end) {
        return format_errc(EINVAL, "proc %p is not valid proc pointer", proc);
    }
    if (atomic_load_explicit(&proc->refcount, memory_order_acquire) == 0) {
        return format_errc(EOWNERDEAD, "proc %p already freed", proc);
    }
    old_fd = __atomic_exchange_n(&proc->sock_fd, -1, memory_order_acq_rel);
    if (old_fd == -1) {
        // We were already disconnected, so this does nothing
        return format_errc(ENOTCONN, "proc %p not connected", proc);
    }
    (void)close(old_fd);
    if (atomic_fetch_sub_explicit(&proc->refcount, 1, memory_order_acq_rel) ==
        1) {
        cleanup_proc(proc);
    }
    return 0;
}

bool monad_event_proc_is_connected(struct monad_event_proc const *proc)
{
    struct pollfd pfd;
    if (proc < s_procs || proc > s_procs_end ||
        atomic_load_explicit(&proc->refcount, memory_order_acquire) < 1) {
        return false;
    }
    pfd.fd = proc->sock_fd;
    pfd.events = POLLOUT;
    return poll(&pfd, 1, 0) == 1 && pfd.revents == POLLOUT;
}

int monad_event_proc_import_ring(
    struct monad_event_proc *proc, enum monad_event_ring_type ring_type,
    struct monad_event_imported_ring **import_p)
{
    int saved_error;
    unsigned oldrc;
    unsigned alloc_bit;
    struct monad_event_imported_ring *import;

    if (import_p == nullptr) {
        return format_errc(EINVAL, "import_p cannot be nullptr");
    }
    *import_p = nullptr;

    // Safely take a reference to proc: the imported ring will keep it alive
    // even if it's disconnected
    if (proc < s_procs || proc > s_procs_end) {
        return format_errc(EINVAL, "proc %p is not valid proc pointer", proc);
    }
    oldrc = atomic_load_explicit(&proc->refcount, memory_order_acquire);
TryPinProc:
    if (oldrc == 0) {
        return format_errc(EOWNERDEAD, "proc %p was already freed", proc);
    }
    if (!atomic_compare_exchange_weak_explicit(
            &proc->refcount,
            &oldrc,
            oldrc + 1,
            memory_order_acq_rel,
            memory_order_acquire)) {
        goto TryPinProc;
    }

    // Allocate an imported ring object
    if (!try_alloc_bit(&s_import_bitmap, &alloc_bit)) {
        saved_error =
            format_errc(ENOBUFS, "no free monad_proc structures available");
        goto UnpinProc;
    }
    import = &s_imports[alloc_bit - 1];
    memset(import, 0, sizeof *import);
    import->type = ring_type;
    import->proc = proc;
    if ((saved_error = import_ring(import)) != 0) {
        free_bit(&s_import_bitmap, alloc_bit);
        goto UnpinProc;
    }
    // Several large pages of the payload buffer are mapped immediately after
    // the end so we can bulk copy near the end without complex index
    // calculations. For languages like Rust, we want to know the "true" size
    // of the payload buffer, e.g., for slices.
    import->true_payload_buf_size =
        import->ring.payload_buf_size + MONAD_EVENT_MAX_PAYLOAD_BUF_SIZE;
    atomic_store_explicit(&import->refcount, 1, memory_order_release);
    pthread_mutex_lock(&proc->mtx);
    TAILQ_INSERT_TAIL(&proc->imports, import, next);
    pthread_mutex_unlock(&proc->mtx);
    *import_p = import;
    return 0;

UnpinProc:
    // Import failed, so release our refcount on proc
    if (atomic_fetch_sub_explicit(&proc->refcount, 1, memory_order_acq_rel) ==
        1) {
        cleanup_proc(proc);
    }
    return saved_error;
}

struct monad_event_imported_ring *
monad_event_imported_ring_acquire(struct monad_event_imported_ring *import)
{
    unsigned oldrc;

    if (import < s_imports || import > s_imports_end) {
        format_errc(EINVAL, "imported ring %p is not a valid pointer", import);
        return nullptr;
    }
    oldrc = atomic_load_explicit(&import->refcount, memory_order_acquire);
TryAgain:
    if (oldrc == 0) {
        format_errc(EOWNERDEAD, "imported ring %p was already freed", import);
        return nullptr;
    }
    if (!atomic_compare_exchange_weak_explicit(
            &import->refcount,
            &oldrc,
            oldrc + 1,
            memory_order_acq_rel,
            memory_order_acquire)) {
        goto TryAgain;
    }
    return import;
}

bool monad_event_imported_ring_release(struct monad_event_imported_ring *import)
{
    unsigned oldrc;

    if (import < s_imports || import > s_imports_end) {
        format_errc(EINVAL, "imported ring %p is not a valid pointer", import);
        return false;
    }
    oldrc = atomic_load_explicit(&import->refcount, memory_order_acquire);
TryAgain:
    if (oldrc == 0) {
        format_errc(EOWNERDEAD, "imported ring %p was already freed", import);
        return false;
    }
    if (!atomic_compare_exchange_weak_explicit(
            &import->refcount,
            &oldrc,
            oldrc - 1,
            memory_order_acq_rel,
            memory_order_acquire)) {
        goto TryAgain;
    }
    if (oldrc == 1) {
        cleanup_imported_ring(import);
        return true;
    }
    return false;
}

int monad_event_imported_ring_init_iter(
    struct monad_event_imported_ring const *import,
    struct monad_event_iterator *iter)
{
    if (import < s_imports || import > s_imports_end) {
        return format_errc(
            EINVAL, "imported ring %p is not a valid pointer", import);
    }
    if (iter == nullptr) {
        return format_errc(EINVAL, "iter cannot be nullptr");
    }
    if (atomic_load_explicit(&import->refcount, memory_order_acquire) == 0) {
        return format_errc(
            EOWNERDEAD, "imported ring %p was already freed", import);
    }
    iter->desc_table = import->ring.descriptor_table;
    iter->payload_buf = import->ring.payload_buf;
    iter->payload_buf_size = import->ring.payload_buf_size;
    iter->capacity_mask = import->ring.capacity - 1;
    iter->wr_state = &import->ring.control->wr_state;
    iter->buffer_window_start = &import->ring.control->buffer_window_start;
    (void)monad_event_iterator_reset(iter);
    return 0;
}

char const *monad_event_proc_get_last_error()
{
    return error_buf;
}
