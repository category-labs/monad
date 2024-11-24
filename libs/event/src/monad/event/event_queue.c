#include <assert.h>
#include <errno.h>
#include <stdarg.h>
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
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_queue.h>
#include <monad/event/event_reader.h>

#include "event_queue_internal.h"

union server_response
{
    enum monad_event_msg_type msg_type;
    struct monad_event_open_error_msg err_msg;
    struct monad_event_open_success_msg ok_msg;
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

static void add_queue_option_defaults(
    struct monad_event_queue_options const *user_opts,
    struct monad_event_queue_options *opts)
{
    *opts = *user_opts;
    if (opts->socket_path == nullptr || *opts->socket_path == '\0') {
        opts->socket_path = MONAD_EVENT_DEFAULT_SOCKET_PATH;
    }
}

static int
map_ring_control(struct monad_event_ring *ring, struct msghdr const *mhdr)
{
    struct monad_event_open_success_msg *msg;
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
    ring->capacity_mask = ring->capacity - 1;
    ring->control_fd = *(int *)CMSG_DATA(cmsg);
    ring->control = mmap(
        nullptr,
        (size_t)getpagesize(),
        PROT_READ,
        MAP_SHARED,
        ring->control_fd,
        0);
    if (ring->control == MAP_FAILED) {
        return format_errc(
            errno, "unable to map ring control segment into process");
    }
    return 0;
}

static int
map_descriptor_table(struct monad_event_ring *ring, struct msghdr const *mhdr)
{
    size_t const PAGE_2MB = (1UL << 21); // x64 2MiB large page
    struct cmsghdr const *cmsg = CMSG_FIRSTHDR(mhdr);
    struct monad_event_open_success_msg const *const msg =
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
    ring->descriptor_table_fd = *(int *)CMSG_DATA(cmsg);

    ring->descriptor_table = mmap(
        nullptr,
        desc_table_map_len + PAGE_2MB,
        PROT_READ,
        MAP_ANONYMOUS | MAP_SHARED | MAP_HUGETLB,
        -1,
        0);
    if (ring->descriptor_table == MAP_FAILED) {
        return format_errc(
            errno, "mmap(2) unable to reserve descriptor VM region");
    }
    if (mmap(
            ring->descriptor_table,
            desc_table_map_len,
            PROT_READ,
            MAP_FIXED | MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
            ring->descriptor_table_fd,
            0) == MAP_FAILED) {
        return format_errc(errno, "unable to remap ring descriptor table");
    }
    if (mmap(
            (uint8_t *)ring->descriptor_table + desc_table_map_len,
            PAGE_2MB,
            PROT_READ,
            MAP_FIXED | MAP_SHARED | MAP_HUGETLB,
            ring->descriptor_table_fd,
            0) == MAP_FAILED) {
        return format_errc(
            errno, "unable to remap wrap-around ring descriptor page");
    }
    return 0;
}

static int
map_payload_page(struct monad_event_queue *queue, struct msghdr const *mhdr)
{
    int memfd;
    struct stat memfd_stat;
    int saved_error;
    struct cmsghdr const *cmsg = CMSG_FIRSTHDR(mhdr);
    struct monad_event_open_success_msg const *const msg =
        mhdr->msg_iov[0].iov_base;

    if (cmsg == nullptr || cmsg->cmsg_level != SOL_SOCKET ||
        cmsg->cmsg_type != SCM_RIGHTS) {
        return format_errc(
            EPROTO,
            "expected MAP_PAYLOAD_PAGE message to "
            "carry a memfd descriptor");
    }
    memfd = *(int *)CMSG_DATA(cmsg);
    if (fstat(memfd, &memfd_stat) == -1) {
        saved_error = format_errc(errno, "fstat(2) of payload page failed");
        (void)close(memfd);
        return saved_error;
    }
    if (queue->num_payload_pages == 0) {
        queue->num_payload_pages = msg->payload_page_pool_size;
        queue->payload_pages =
            calloc(queue->num_payload_pages, sizeof(queue->payload_pages[0]));
        if (queue->payload_pages == nullptr) {
            saved_error =
                format_errc(errno, "calloc(3) for payload_page_headers failed");
            (void)close(memfd);
            return saved_error;
        }
    }
    queue->payload_pages[msg->page_id] = mmap(
        nullptr,
        (size_t)memfd_stat.st_size,
        PROT_READ,
        MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
        memfd,
        0);
    if (queue->payload_pages[msg->page_id] == MAP_FAILED) {
        saved_error = format_errc(errno, "unable to map payload page");
        (void)close(memfd);
        return saved_error;
    }
    // TODO(ken): we're closing this so we don't leak it, which is different
    //   that what we do for the event ring memfds; should probably be
    //   consistent?
    (void)close(memfd);
    return 0;
}

static int set_metadata_table(
    struct monad_event_open_success_msg const *msg,
    struct monad_event_queue *queue, void const **table)
{
    size_t page_len;
    if (table == nullptr) {
        return 0;
    }
    if (queue->num_payload_pages <= msg->page_id ||
        queue->payload_pages[msg->page_id] == nullptr) {
        return format_errc(
            EPROTO,
            "saw METADATA_OFFSET message before "
            "expected metadata page %hhu:%hu",
            queue->type,
            msg->page_id);
    }
    page_len = (size_t)(queue->payload_pages[msg->page_id]->heap_end -
                        (uint8_t *)queue->payload_pages[msg->page_id]);
    if (page_len <= msg->metadata_offset) {
        return format_errc(
            EPROTO,
            "protocol advertised out-of-bounds offset on metadata page "
            "%hhu:%hu",
            queue->type,
            msg->page_id);
    }
    switch (msg->metadata_type) {
    case MONAD_EVENT_METADATA_THREAD:
        [[fallthrough]];
    case MONAD_EVENT_METADATA_BLOCK_FLOW:
        *table = (uint8_t const *)queue->payload_pages[msg->page_id] +
                 msg->metadata_offset;
        return 0;
    default:
        return format_errc(
            EPROTO, "unknown metadata map type %hhu", msg->metadata_type);
    }
}

static int open_queue(
    struct monad_event_queue *queue, enum monad_event_queue_type queue_type,
    struct monad_event_thread_info const **thread_table,
    struct monad_event_block_exec_header const **block_header_table)
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
    struct monad_event_open_queue_msg open_msg = {
        .msg_type = MONAD_EVENT_MSG_OPEN_QUEUE, .queue_type = queue_type};
    memcpy(
        open_msg.event_metadata_hash,
        g_monad_event_metadata_hash,
        sizeof open_msg.event_metadata_hash);
    queue->type = queue_type;

    // The process of opening an event queue is:
    //
    //   1. We send a MONAD_EVENT_MSG_OPEN_QUEUE message to the server
    //
    //   2. The server sends several messages in response. Most of the
    //      response messages describe a single shared memory segment and bear
    //      a memfd_create(2) file descriptor as ancillary cmsg data.
    //
    // The message types send in response are:
    //
    //   MONAD_EVENT_MSG_OPEN_ERROR - if this message is seen, the open process
    //       has failed, and no more messages will be sent
    //
    //   MONAD_EVENT_MSG_MAP_RING_CONTROL - file descriptor of the event ring
    //       control page segment
    //
    //   MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE - file descriptor of the event
    //       descriptor table
    //
    //   MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE - file descriptor of a single payload
    //       page (there is an array of these)
    //
    //   MONAD_EVENT_MSG_METADATA_OFFSET - explains where in a particular
    //       payload page one of the metadata arrays is located; the
    //       MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE for that page will already have
    //       been received
    //
    //   MONAD_EVENT_MSG_OPEN_FINISHED - if this message is seen, the open
    //       process completed successfully

    if (send(queue->sock_fd, &open_msg, sizeof open_msg, 0) !=
        sizeof open_msg) {
        return format_errc(errno, "send(2) of OPEN_QUEUE message failed");
    }
    response.msg_type = MONAD_EVENT_MSG_NONE;
    while (response.msg_type != MONAD_EVENT_MSG_OPEN_FINISHED) {
        if (recvmsg(queue->sock_fd, &mhdr, 0) == -1) {
            return format_errc(errno, "recvmsg(2) from event server failed");
        }

        switch (response.msg_type) {
        case MONAD_EVENT_MSG_OPEN_ERROR:
            rc = response.err_msg.error_code != 0 ? response.err_msg.error_code
                                                  : EIO;
            return format_errc(
                rc,
                "event server reported error: %s",
                response.err_msg.error_buf);

        case MONAD_EVENT_MSG_MAP_RING_CONTROL:
            if ((rc = map_ring_control(&queue->event_ring, &mhdr)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE:
            if ((rc = map_descriptor_table(&queue->event_ring, &mhdr)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE:
            if ((rc = map_payload_page(queue, &mhdr)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_METADATA_OFFSET:
            if ((rc = set_metadata_table(
                     &response.ok_msg,
                     queue,
                     response.ok_msg.metadata_type ==
                             MONAD_EVENT_METADATA_THREAD
                         ? (void const **)thread_table
                         : (void const **)block_header_table)) != 0) {
                return rc;
            }
            break;

        case MONAD_EVENT_MSG_OPEN_FINISHED:
            // Signifies the end of the open session sequence
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

int monad_event_queue_connect(
    struct monad_event_queue_options const *user_opts,
    struct monad_event_queue **queue_p,
    struct monad_event_thread_info const **thread_table,
    struct monad_event_block_exec_header const **block_header_table)
{
    int saved_error;
    struct sockaddr_un server_addr;
    struct monad_event_queue *queue;
    struct monad_event_queue_options opts;

    if (user_opts == nullptr) {
        return format_errc(EINVAL, "user_opts cannot be nullptr");
    }
    if (queue_p == nullptr) {
        return format_errc(EFAULT, "queue cannot be nullptr");
    }

    // Even when the options are explicitly supplied, some values may have a
    // "use default" sentinel value (e.g., 0) that needs to be replaced
    add_queue_option_defaults(user_opts, &opts);

    queue = *queue_p = malloc(sizeof *queue);
    if (queue == nullptr) {
        return format_errc(errno, "malloc(3) error");
    }
    memset(queue, 0, sizeof *queue);

    // Set all the file descriptors to -1 in case we cleanup early (so we
    // don't accidentally close fd 0)
    queue->sock_fd = queue->event_ring.control_fd =
        queue->event_ring.descriptor_table_fd = -1;

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
    queue->sock_fd = socket(AF_LOCAL, SOCK_SEQPACKET, 0);
    if (queue->sock_fd == -1) {
        saved_error = format_errc(errno, "socket(2) failed");
        goto Cleanup;
    }
    if ((opts.socket_timeout.tv_sec != 0 || opts.socket_timeout.tv_usec != 0) &&
        setsockopt(
            queue->sock_fd,
            SOL_SOCKET,
            SO_RCVTIMEO,
            &opts.socket_timeout,
            sizeof opts.socket_timeout) == -1) {
        saved_error =
            format_errc(errno, "unable to set SO_RCVTIMEO for client socket");
        goto Cleanup;
    }
    if (connect(
            queue->sock_fd,
            (struct sockaddr const *)&server_addr,
            sizeof server_addr) == -1) {
        saved_error = format_errc(
            errno,
            "unable to connect to event server socket endpoint `%s`",
            server_addr.sun_path);
        goto Cleanup;
    }

    // Open the event session, after which the queue is ready for use
    saved_error =
        open_queue(queue, opts.queue_type, thread_table, block_header_table);
    if (saved_error != 0) {
        goto Cleanup;
    }
    return 0;

Cleanup:
    monad_event_queue_disconnect(queue);
    *queue_p = nullptr;
    return saved_error;
}

void monad_event_queue_disconnect(struct monad_event_queue *queue)
{
    struct monad_event_payload_page const *page;
    struct monad_event_ring *ring;
    size_t map_len;

    assert(queue != nullptr);
    (void)close(queue->sock_fd);

    // Remove the event descriptor ring mappings
    ring = &queue->event_ring;
    if (ring->descriptor_table != nullptr) {
        map_len = ring->capacity * sizeof(struct monad_event_descriptor);
        munmap(ring->descriptor_table, map_len);
        munmap((uint8_t *)ring->descriptor_table + map_len, 1UL << 21);
    }
    (void)close(ring->descriptor_table_fd);
    if (queue->event_ring.control != nullptr) {
        munmap(queue->event_ring.control, (size_t)getpagesize());
    }
    (void)close(queue->event_ring.control_fd);

    // Unmap all the payload pages
    for (uint16_t p = 0; p < queue->num_payload_pages; ++p) {
        page = queue->payload_pages[p];
        if (page != nullptr) {
            map_len = (size_t)(page->heap_end - page->page_base);
            (void)munmap((void *)page, map_len);
        }
    }

    // Free all the dynamic memory
    free(queue->payload_pages);
    free(queue);
}

bool monad_event_queue_is_connected(struct monad_event_queue const *queue)
{
    struct pollfd pfd;
    if (queue == nullptr) {
        return false;
    }
    pfd.fd = queue->sock_fd;
    pfd.events = POLLOUT;
    return poll(&pfd, 1, 0) == 1 && pfd.revents == POLLOUT;
}

uint64_t monad_event_queue_init_reader(
    struct monad_event_queue const *queue, struct monad_event_reader *reader,
    struct monad_event_queue_ffi_extra *ffi_extra)
{
    reader->desc_table = queue->event_ring.descriptor_table;
    reader->payload_pages = queue->payload_pages;
    reader->capacity_mask = queue->event_ring.capacity_mask;
    reader->prod_next = &queue->event_ring.control->prod_next;
    if (ffi_extra != nullptr) {
        ffi_extra->desc_table_size =
            queue->event_ring.capacity + MONAD_EVENT_MAX_BULK_COPY;
        ffi_extra->num_payload_pages = queue->num_payload_pages;
    }
    return monad_event_reader_reset(reader);
}

char const *monad_event_queue_get_last_error()
{
    return error_buf;
}
