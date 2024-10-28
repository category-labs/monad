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

#include <monad/event/event_consumer.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>

static struct monad_event_queue_options g_default_queue_options = {
    .socket_path = MONAD_EVENT_DEFAULT_SOCKET_PATH,
    .socket_timeout = {.tv_sec = 1, .tv_usec = 0},
    .ring_shift = MONAD_EVENT_CONSUMER_DEFAULT_RING_SHIFT};

union server_response
{
    enum monad_event_msg_type msg_type;
    struct monad_event_session_error_msg err_msg;
    struct monad_event_session_success_msg ok_msg;
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

#define BLOCK_SIZE ((1600 - 2 * 256) / 8)

extern size_t
SHA3_absorb(uint64_t A[5][5], const unsigned char *inp, size_t len, size_t r);

extern void SHA3_squeeze(
    uint64_t A[5][5], unsigned char *out, size_t len, size_t r, int next);

static void keccak256(
    unsigned char const *const in, unsigned long const len,
    unsigned char out[32])
{
    uint64_t A[5][5];
    unsigned char blk[BLOCK_SIZE];

    __builtin_memset(A, 0, sizeof(A));

    size_t const rem = SHA3_absorb(A, in, len, BLOCK_SIZE);
    __builtin_memcpy(blk, &in[len - rem], rem);
    __builtin_memset(&blk[rem], 0, BLOCK_SIZE - rem);
    blk[rem] = 0x01;
    blk[BLOCK_SIZE - 1] |= 0x80;
    (void)SHA3_absorb(A, blk, BLOCK_SIZE, BLOCK_SIZE);

    SHA3_squeeze(A, out, 32, BLOCK_SIZE, 0);
}

static void add_queue_option_defaults(
    struct monad_event_queue_options const *user_opts,
    struct monad_event_queue_options *opts)
{
    if (user_opts == nullptr) {
        user_opts = &g_default_queue_options;
    }
    *opts = *user_opts;
    if (opts->socket_path == nullptr || *opts->socket_path == '\0') {
        opts->socket_path = MONAD_EVENT_DEFAULT_SOCKET_PATH;
    }
    if (opts->ring_shift == 0) {
        opts->ring_shift = MONAD_EVENT_CONSUMER_DEFAULT_RING_SHIFT;
    }
}

static int
map_ring_control(struct monad_event_ring *ring, struct msghdr const *mhdr)
{
    struct monad_event_session_success_msg *msg;
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
        PROT_READ | PROT_WRITE,
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
    struct monad_event_session_success_msg const *const msg =
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
        PROT_WRITE,
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
            PROT_WRITE,
            MAP_FIXED | MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
            ring->descriptor_table_fd,
            0) == MAP_FAILED) {
        return format_errc(errno, "unable to remap ring descriptor table");
    }
    if (mmap(
            (uint8_t *)ring->descriptor_table + desc_table_map_len,
            PAGE_2MB,
            PROT_WRITE,
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
    struct monad_event_payload_page *page;
    struct cmsghdr const *cmsg = CMSG_FIRSTHDR(mhdr);

    if (cmsg == nullptr || cmsg->cmsg_level != SOL_SOCKET ||
        cmsg->cmsg_type != SCM_RIGHTS) {
        return format_errc(
            EPROTO,
            "expected MAP_PAYLOAD_PAGE message to "
            "carry a memfd descriptor");
    }
    memfd = *(int *)CMSG_DATA(cmsg);
    if (fstat(memfd, &memfd_stat) == -1) {
        saved_error = errno;
        (void)close(memfd);
        return format_errc(saved_error, "fstat(2) of payload page failed");
    }

    if (queue->payload_page_size + 1 > queue->payload_page_capacity) {
        queue->payload_page_capacity *= 2;
        queue->payload_pages = reallocarray(
            queue->payload_pages,
            queue->payload_page_capacity,
            sizeof(struct monad_event_payload_page));
        if (queue->payload_pages == nullptr) {
            return format_errc(
                errno, "reallocarray(3) for payload_pages failed");
        }
    }
    page = &queue->payload_pages[queue->payload_page_size];
    page->page_header = mmap(
        nullptr,
        (size_t)memfd_stat.st_size,
        PROT_READ,
        MAP_SHARED | MAP_HUGETLB | MAP_POPULATE,
        memfd,
        0);
    if (page->page_header == MAP_FAILED) {
        saved_error = errno;
        (void)close(memfd);
        return format_errc(saved_error, "unable to map payload page");
    }
    page->map_len = (size_t)memfd_stat.st_size;
    ++queue->payload_page_size;
    return 0;
}

static int send_open_session_msg(int sock_fd, uint8_t ring_shift)
{
    int rc;
    char *domain_meta_buf;
    size_t domain_meta_buf_size;
    struct monad_event_domain_metadata const *domain_meta;
    struct monad_event_client_domain_info domain_info[64];
    struct monad_event_open_session_msg open_msg = {
        .msg_type = MONAD_EVENT_MSG_OPEN_SESSION,
        .ring_shift = ring_shift,
        .domain_count = 0};
    struct iovec msg_iov[] = {
        [0] = {.iov_base = &open_msg, .iov_len = sizeof open_msg},
        [1] = {.iov_base = domain_info, .iov_len = 0}}; // To be set below
    struct msghdr mhdr = {
        .msg_name = nullptr,
        .msg_namelen = 0,
        .msg_iov = msg_iov,
        .msg_iovlen = sizeof msg_iov / sizeof msg_iov[0],
        .msg_control = nullptr,
        .msg_controllen = 0};

    for (size_t i = 0; i < g_monad_event_domain_meta_size; ++i) {
        domain_meta = &g_monad_event_domain_meta[i];
        if (domain_meta->domain == MONAD_EVENT_DOMAIN_NONE) {
            continue;
        }
        rc = monad_event_metadata_serialize(
            domain_meta, &domain_meta_buf, &domain_meta_buf_size);
        if (rc != 0) {
            return format_errc(
                rc,
                "monad_event_metadata_serialize failed "
                "for domain `%s` (%hhu)",
                domain_meta->name,
                domain_meta->domain);
        }
        domain_info[open_msg.domain_count].domain_code = domain_meta->domain;
        keccak256(
            (uint8_t const *)domain_meta_buf,
            domain_meta_buf_size,
            domain_info[open_msg.domain_count++].domain_metadata_hash);
        free(domain_meta_buf);
    }
    msg_iov[1].iov_len = sizeof domain_info[0] * open_msg.domain_count;
    if (sendmsg(sock_fd, &mhdr, 0) !=
        (ssize_t)(msg_iov[0].iov_len + msg_iov[1].iov_len)) {
        return format_errc(errno, "sendmsg(2) of OPEN_SESSION message failed");
    }
    return 0;
}

static int open_session(struct monad_event_queue *queue, uint8_t ring_shift)
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

    if ((rc = send_open_session_msg(queue->sock_fd, ring_shift)) != 0) {
        return rc;
    }
    response.msg_type = MONAD_EVENT_MSG_NONE;
    while (response.msg_type != MONAD_EVENT_MSG_SESSION_OPEN) {
        if (recvmsg(queue->sock_fd, &mhdr, 0) == -1) {
            return format_errc(errno, "recvmsg(2) from event server failed");
        }

        switch (response.msg_type) {
        case MONAD_EVENT_MSG_SESSION_ERROR:
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

        case MONAD_EVENT_MSG_SESSION_OPEN:
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

int monad_event_queue_create(
    struct monad_event_queue_options const *user_opts,
    struct monad_event_queue **queue_p)
{
    int saved_error;
    struct sockaddr_un server_addr;
    struct monad_event_queue *queue;
    struct monad_event_queue_options opts;

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

    saved_error = pthread_spin_init(&queue->lock, /*pshared=*/0);
    if (saved_error != 0) {
        format_errc(saved_error, "pthread_spin_init(3) error");
        free(queue);
        *queue_p = nullptr;
        return saved_error;
    }

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

    // We don't know how many payload pages there will be; guess a reasonable
    // size and we'll call reallocarray(3) later if more are needed
    queue->payload_page_capacity = 64;
    queue->payload_pages = calloc(
        queue->payload_page_capacity, sizeof(struct monad_event_payload_page));
    if (queue->payload_pages == nullptr) {
        saved_error =
            format_errc(errno, "calloc(3) of payload_page_count failed");
        goto Cleanup;
    }

    // Open the event session, after which the queue is ready for use
    saved_error = open_session(queue, opts.ring_shift);
    if (saved_error != 0) {
        goto Cleanup;
    }
    return 0;

Cleanup:
    monad_event_queue_destroy(queue);
    *queue_p = nullptr;
    return saved_error;
}

void monad_event_queue_destroy(struct monad_event_queue *queue)
{
    struct monad_event_payload_page *page;
    struct monad_event_ring *ring;
    size_t desc_table_map_len;

    assert(queue != nullptr);
    pthread_spin_destroy(&queue->lock);
    (void)close(queue->sock_fd);

    // Remove the event descriptor ring mappings
    ring = &queue->event_ring;
    if (ring->descriptor_table != nullptr) {
        desc_table_map_len =
            ring->capacity * sizeof(struct monad_event_descriptor);
        munmap(ring->descriptor_table, desc_table_map_len);
        munmap(
            (uint8_t *)ring->descriptor_table + desc_table_map_len, 1UL << 21);
    }
    (void)close(ring->descriptor_table_fd);
    if (queue->event_ring.control != nullptr) {
        munmap(queue->event_ring.control, (size_t)getpagesize());
    }
    (void)close(queue->event_ring.control_fd);

    // Unmap all the payload pages
    for (uint8_t p = 0; p < queue->payload_page_size; ++p) {
        page = &queue->payload_pages[p];
        (void)munmap(page->page_header, page->map_len);
    }

    // Free all the dynamic memory
    free(queue->payload_pages);
    free(queue);
}

int monad_event_queue_set_domain_mask(
    struct monad_event_queue *queue, uint64_t desired_mask,
    uint64_t *recorder_mask, uint64_t *effective_mask, uint64_t *prev_mask)
{
    union server_response response;
    int saved_error;
    struct monad_event_set_domain_mask_msg const msg = {
        .msg_type = MONAD_EVENT_MSG_SET_DOMAIN_MASK,
        .domain_mask = desired_mask};

    if (queue == nullptr) {
        return format_errc(EFAULT, "queue cannot be nullptr");
    }
    pthread_spin_lock(&queue->lock);
    if (send(queue->sock_fd, &msg, sizeof msg, 0) != sizeof msg) {
        saved_error =
            format_errc(errno, "send(2) of SET_DOMAIN_MASK message failed");
        goto Cleanup;
    }
    if (recv(queue->sock_fd, &response, sizeof response, 0) == -1) {
        saved_error =
            format_errc(errno, "recv(2) of SET_DOMAIN_MASK response failed");
        goto Cleanup;
    }
    if (response.msg_type == MONAD_EVENT_MSG_SESSION_ERROR) {
        saved_error = response.err_msg.error_code != 0
                          ? response.err_msg.error_code
                          : EIO;
        format_errc(
            saved_error,
            "event server responded with error: %s",
            response.err_msg.error_buf);
        goto Cleanup;
    }
    if (response.msg_type != MONAD_EVENT_MSG_NEW_DOMAIN_MASK) {
        saved_error = format_errc(
            EPROTO, "unexpected response %u from server", response.msg_type);
        goto Cleanup;
    }
    if (prev_mask != nullptr) {
        *prev_mask = queue->domain_mask;
    }
    queue->domain_mask = desired_mask;
    if (recorder_mask != nullptr) {
        *recorder_mask = response.ok_msg.recorder_domain_mask;
    }
    if (effective_mask != nullptr) {
        *effective_mask = response.ok_msg.effective_domain_mask;
    }
    saved_error = 0;

Cleanup:
    pthread_spin_unlock(&queue->lock);
    return saved_error;
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

char const *monad_event_get_last_error()
{
    return error_buf;
}
