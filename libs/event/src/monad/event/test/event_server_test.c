/**
 * @file
 *
 * This file implements the OPEN_QUEUE message for a fake event server, when
 * it is opening a pre-recorded snapshot of some shared memory segments.
 */

#include <assert.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <syslog.h>
#include <unistd.h>

#include <monad/core/srcloc.h>
#include <monad/event/event.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_server.h>
#include <monad/event/event_server_internal.h>
#include <monad/event/event_shared.h>

static void write_msg(int severity, char const *msg, void *file)
{
    if (file != nullptr) {
        fprintf((FILE *)file, "test_server[%d]: %s\n", severity, msg);
    }
}

__attribute__((format(printf, 5, 6))) static int write_log(
    FILE *out, int severity, int err, monad_source_location_t const *srcloc,
    char const *format, ...)
{
    va_list ap;
    static thread_local char errbuf[1024];

    va_start(ap, format);
    _monad_event_vformat_err(errbuf, sizeof errbuf, srcloc, err, format, ap);
    va_end(ap);
    write_msg(severity, errbuf, out);
    return err;
}

static size_t round_size_to_align(size_t size, size_t align)
{
    return (size + (align - 1)) & ~(align - 1);
}

// Redefinition of structure from exportshm.cpp
struct test_file_segment
{
    uint32_t type;
    uint16_t page_id;
    uint16_t metadata_type;
    uint64_t length;
    uint64_t offset;
};

struct mapped_test_segment
{
    void *map_base;
    size_t map_len;
    int memfd;
};

struct test_server_context
{
    struct test_file_segment const *segments;
    size_t segment_count;
    size_t map_len;
    struct mapped_test_segment *mapped_segments;
    size_t ring_capacity;
    size_t page_pool_size;
    uint8_t const *metadata_hash;
    bool unmap_on_close;
};

static void
cleanup_test_server_resources(struct test_server_context *test_context)
{
    struct mapped_test_segment *mapped_seg;
    assert(test_context != nullptr);
    for (size_t s = 0; s < test_context->segment_count; ++s) {
        mapped_seg = &test_context->mapped_segments[s];
        (void)munmap(mapped_seg->map_base, mapped_seg->map_len);
        (void)close(mapped_seg->memfd);
    }
    free(test_context->mapped_segments);
    if (test_context->unmap_on_close) {
        (void)munmap((void *)test_context->segments, test_context->map_len);
    }
    free(test_context);
}

static bool export_test_shared_memory_to_client(
    struct monad_event_open_queue_msg const *open_msg, int sock_fd,
    unsigned client_id, close_client_err_fn *close_fn,
    struct monad_event_client *client, void *arg, unsigned *nmsgs)
{
    // Similar to export_recorder_shared_memory_to_client, but for the fake
    // server for test cases
    union
    {
        char buf[CMSG_SPACE(sizeof(int))];
        struct cmsghdr hdr;
    } cmsg;
    struct monad_event_open_success_msg msg;
    struct iovec msg_iov[1] = {[0] = {.iov_base = &msg, .iov_len = sizeof msg}};
    struct msghdr mhdr = {
        .msg_name = nullptr,
        .msg_namelen = 0,
        .msg_iov = msg_iov,
        .msg_iovlen = 1,
        .msg_control = cmsg.buf,
        .msg_controllen = sizeof cmsg,
        .msg_flags = 0};
    struct test_server_context *const test_context = arg;

    if (memcmp(
            open_msg->event_metadata_hash,
            test_context->metadata_hash,
            sizeof open_msg->event_metadata_hash) != 0) {
        close_fn(
            client, EINVAL, "client metadata hash does not match server hash");
        return false;
    }

    cmsg.hdr.cmsg_level = SOL_SOCKET;
    cmsg.hdr.cmsg_type = SCM_RIGHTS;
    cmsg.hdr.cmsg_len = CMSG_LEN(sizeof(int));

    memset(&msg, 0, sizeof msg);
    msg.ring_capacity = test_context->ring_capacity;
    msg.payload_page_pool_size = (uint16_t)test_context->page_pool_size;
    msg.cur_seqno = 0;
    for (size_t s = 0; s < test_context->segment_count; ++s) {
        struct test_file_segment const *segment = &test_context->segments[s];
        struct mapped_test_segment const *mapped_seg =
            &test_context->mapped_segments[s];

        msg.msg_type = (enum monad_event_msg_type)segment->type;
        switch (msg.msg_type) {
        case MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE:
            msg.page_id = segment->page_id;
            [[fallthrough]];
        case MONAD_EVENT_MSG_MAP_RING_CONTROL:
            [[fallthrough]];
        case MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE:
            msg.metadata_type = MONAD_EVENT_METADATA_NONE;
            msg.metadata_offset = 0;
            *(int *)CMSG_DATA(&cmsg.hdr) = mapped_seg->memfd;
            if (sendmsg(sock_fd, &mhdr, 0) == -1) {
                close_fn(
                    client,
                    errno,
                    "unable to export memfd segment %lu (type %u) to client %u",
                    s,
                    segment->type,
                    client_id);
                return false;
            }
            break;

        case MONAD_EVENT_MSG_METADATA_OFFSET:
            msg.metadata_type = (uint8_t)segment->metadata_type;
            msg.metadata_offset = (uint32_t)segment->offset;
            msg.page_id = segment->page_id;
            *(int *)CMSG_DATA(&cmsg.hdr) = 0;
            if (sendmsg(sock_fd, &mhdr, 0) == -1) {
                close_fn(
                    client,
                    errno,
                    "unable to export offset mapping %lu (type %u) to client "
                    "%u",
                    s,
                    segment->type,
                    client_id);
                return false;
            }
            break;

        default:
            assert("unexpected message type");
        }
        ++*nmsgs;
    }

    // Send the final message
    msg.msg_type = MONAD_EVENT_MSG_OPEN_FINISHED;
    mhdr.msg_control = nullptr;
    mhdr.msg_controllen = 0;
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        close_fn(client, errno, "unable to send final message for queue");
        return false;
    }

    ++*nmsgs;
    return true;
}

static void *accept_one(void *arg0)
{
    unsigned queues_exported = 0;
    struct monad_event_server *const server = arg0;
    (void)pthread_detach(pthread_self());
    while (queues_exported == 0) {
        (void)monad_event_server_process_work(
            server, nullptr, nullptr, &queues_exported);
    }
    return nullptr;
}

static struct shared_mem_export_ops s_export_ops = {
    .cleanup = (void (*)(void *))cleanup_test_server_resources,
    .export = export_test_shared_memory_to_client,
    .heartbeat = nullptr};

#define WR_ERR(ERRNO, ...)                                                     \
    write_log(                                                                 \
        log_file,                                                              \
        LOG_ERR,                                                               \
        (ERRNO),                                                               \
        &(monad_source_location_t){__FUNCTION__, __FILE__, __LINE__, 0},       \
        __VA_ARGS__)

/// Creates a "fake" server, used only for testing the event queue client
/// libraries with static test data that is present in memory; the static
/// test data is typically embedded into the test binary using #embed in C or
/// include_bytes! in Rust
int monad_event_test_server_create_from_bytes(
    char const *socket_path, FILE *log_file, void const *capture_data,
    size_t capture_len, bool unmap_on_close,
    struct monad_event_server **server_p)
{
    int saved_error;
    unsigned map_flags;
    struct test_server_context *test_context;
    struct test_file_segment const *segment;
    char segment_name[32];

    // TODO(ken): for Rust
    log_file = log_file != nullptr ? log_file : stderr;
    struct monad_event_server_options const opts = {
        .log_fn = write_msg,
        .log_context = log_file,
        .socket_path = socket_path};

    if (server_p == nullptr) {
        return WR_ERR(EFAULT, "server_p cannot be nullptr");
    }
    *server_p = nullptr;
    test_context = malloc(sizeof *test_context);
    assert(test_context != nullptr);
    memset(test_context, 0, sizeof *test_context);
    test_context->segments = capture_data;
    test_context->map_len = capture_len;
    test_context->unmap_on_close = unmap_on_close;

    // Compute the number of segments in the file, and create memfds to hold
    // the contents
    segment = test_context->segments;
    while (segment->type != MONAD_EVENT_MSG_NONE) {
        ++test_context->segment_count;
        ++segment;
    }
    test_context->metadata_hash =
        (uint8_t const *)&test_context
            ->segments[test_context->segment_count + 1];
    test_context->mapped_segments = calloc(
        test_context->segment_count, sizeof(test_context->mapped_segments[0]));
    assert(test_context->mapped_segments != MAP_FAILED);

    // For all non-zero length segments, create and map a memfd and copy the
    // segment contents into it. The rationale for doing this is both because
    // we want HUGETLB support (because the client expects it) and because the
    // protocol associates one exported memory segment with one memfd.
    for (size_t s = 0; s < test_context->segment_count; ++s) {
        struct mapped_test_segment *ms = &test_context->mapped_segments[s];
        segment = &test_context->segments[s];
        if (segment->type == MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE) {
            ++test_context->page_pool_size;
        }
        if (segment->length == 0) {
            ms->memfd = -1;
            continue;
        }
        snprintf(segment_name, sizeof segment_name, "tes-%lu", s);
        map_flags =
            segment->type == MONAD_EVENT_MSG_MAP_RING_CONTROL ? 0 : MFD_HUGETLB;
        ms->memfd = memfd_create(segment_name, MFD_CLOEXEC | map_flags);
        if (ms->memfd == -1) {
            saved_error =
                WR_ERR(errno, "unable to memfd_create %s", segment_name);
            test_context->segment_count = s;
            cleanup_test_server_resources(test_context);
            return saved_error;
        }
        ms->map_len = segment->length;
        map_flags = 0;
        if (segment->type != MONAD_EVENT_MSG_MAP_RING_CONTROL) {
            ms->map_len = round_size_to_align(segment->length, 1UL << 21);
            map_flags = MAP_HUGETLB;
        }
        if (segment->type == MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE) {
            test_context->ring_capacity =
                ms->map_len / sizeof(struct monad_event_descriptor);
        }
        if (ftruncate(ms->memfd, (off_t)ms->map_len) == -1) {
            saved_error = WR_ERR(
                errno,
                "unable to ftruncate %s -> %lu",
                segment_name,
                ms->map_len);
        }
        ms->map_base = mmap(
            nullptr,
            ms->map_len,
            PROT_READ | PROT_WRITE,
            MAP_SHARED | (int)map_flags,
            ms->memfd,
            0);
        if (ms->map_base == MAP_FAILED) {
            saved_error = WR_ERR(errno, "unable to mmap %s", segment_name);
            test_context->segment_count = s;
            cleanup_test_server_resources(test_context);
            return saved_error;
        }
        memcpy(
            ms->map_base,
            (uint8_t const *)test_context->segments + segment->offset,
            segment->length);
        if (segment->type == MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE) {
            // We need to fix the internal book-keeping parameters of the
            // copied page, because the client peeks at them to calculate
            // the page size, to munmap(2) it.
            // TODO(ken): client should not be doing that in the first place
            struct monad_event_payload_page *const payload_page = ms->map_base;
            payload_page->heap_end = payload_page->heap_next;
        }
    }

    if ((saved_error = _monad_event_server_create_common(
             &opts, &s_export_ops, test_context, server_p)) != 0) {
        cleanup_test_server_resources(test_context);
        return saved_error;
    }
    return 0;
}

/// Wrapper around monad_event_test_server_create_from_bytes that takes
/// a file as input
int monad_event_test_server_create_from_file(
    char const *socket_path, FILE *log_file, char const *capture_path,
    struct monad_event_server **server_p)
{
    int capture_fd;
    int saved_error;
    void const *map_base;
    size_t map_len;
    struct stat capture_stat;

    if (capture_path == nullptr) {
        return WR_ERR(EFAULT, "capture_path cannot be nullptr");
    }
    // Open the test file, map it into our address space, then close it.
    // Once we have the bytes in a local array, delegate to
    // monad_event_test_server_create_from_bytes
    capture_fd = open(capture_path, O_RDONLY);
    if (capture_fd == -1) {
        return WR_ERR(errno, "unable to open capture file `%s`", capture_path);
    }
    if (fstat(capture_fd, &capture_stat) == -1) {
        saved_error =
            WR_ERR(errno, "unable to stat capture file `%s`", capture_path);
        (void)close(capture_fd);
        return saved_error;
    }
    map_len = (size_t)capture_stat.st_size;
    map_base = mmap(nullptr, map_len, PROT_READ, MAP_SHARED, capture_fd, 0);
    if (map_base == MAP_FAILED) {
        saved_error =
            WR_ERR(errno, "failed mmap of test file: `%s`", capture_path);
        (void)close(capture_fd);
        return saved_error;
    }
    (void)close(capture_fd);
    return monad_event_test_server_create_from_bytes(
        socket_path,
        log_file,
        map_base,
        map_len,
        /*unmap_on_close=*/true,
        server_p);
}

// A simple method used for connecting to test servers. This creates a detached
// thread, waits for a connection to be accepted on that thread, then the
// thread exits.
int monad_event_test_server_accept_one(struct monad_event_server *server)
{
    pthread_t thr;
    return pthread_create(&thr, nullptr, accept_one, server);
}

/// event_server.c depends on this symbol which normally comes from
/// libmonad_core.a, which we don't link to. We don't link its original
/// implementation either, since it is implemented in C++, which we otherwise
/// don't need.
void monad_stack_backtrace_capture_and_print(
    char *, size_t, int fd, unsigned, bool)
{
    dprintf(fd, "<backtrace not implemented>\n");
}
