/**
 * @file
 *
 * This file implements the event ring export logic for event rings whose
 * shared memory segments are owned by a `struct monad_event_recorder` in the
 * libs/core/event library. This is in a separate file for a cleaner
 * separation: this is the only file that accesses the internals of both the
 * event server and event recorder.
 */

#include <stdatomic.h>
#include <string.h>

#include <errno.h>
#include <pthread.h>
#include <sys/socket.h>

#include <monad/core/spinlock.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_recorder.h>

#include "event_server_export.h"

/*
 * To understand the flow of the export process, see the comments for the
 * client side (event_client.c in libs/event)
 */

static bool export_shared_recorder_metadata(
    int sock_fd, unsigned client_id, close_client_err_fn *close_fn,
    struct monad_event_client *client, void *, unsigned *nmsgs)
{
    union
    {
        char buf[CMSG_SPACE(sizeof(int))];
        struct cmsghdr hdr;
    } cmsg;
    struct monad_event_export_success_msg msg;
    struct iovec msg_iov[1] = {[0] = {.iov_base = &msg, .iov_len = sizeof msg}};
    struct msghdr mhdr = {
        .msg_name = nullptr,
        .msg_namelen = 0,
        .msg_iov = msg_iov,
        .msg_iovlen = 1,
        .msg_control = cmsg.buf,
        .msg_controllen = sizeof cmsg,
        .msg_flags = 0};
    struct monad_event_recorder_shared_state *const rss =
        &g_monad_event_recorder_shared_state;

    memset(&msg, 0, sizeof msg);

    cmsg.hdr.cmsg_level = SOL_SOCKET;
    cmsg.hdr.cmsg_type = SCM_RIGHTS;
    cmsg.hdr.cmsg_len = CMSG_LEN(sizeof(int));

    pthread_mutex_lock(&rss->mtx);
    // Send the metadata page
    msg.msg_type = MONAD_EVENT_MSG_MAP_METADATA_PAGE;
    *(int *)CMSG_DATA(&cmsg.hdr) = rss->metadata_page.memfd;
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&rss->mtx);
        close_fn(
            client,
            errno,
            "unable to export metadata page for ring to client %u",
            client_id);
        return false;
    }
    ++*nmsgs;

    // Send the thread table metadata offset message
    msg.msg_type = MONAD_EVENT_MSG_METADATA_OFFSET;
    msg.metadata_type = MONAD_EVENT_METADATA_THREAD;
    monad_event_recorder_export_metadata_section(
        msg.metadata_type, &msg.metadata_offset);
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&rss->mtx);
        close_fn(
            client,
            errno,
            "unable to send thread offset table message to client %u",
            client_id);
        return false;
    }
    ++*nmsgs;

    // Send the block flow table metadata offset message
    msg.metadata_type = MONAD_EVENT_METADATA_BLOCK_FLOW;
    monad_event_recorder_export_metadata_section(
        msg.metadata_type, &msg.metadata_offset);
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&rss->mtx);
        close_fn(
            client,
            errno,
            "unable to send block flow offset table message to client %u",
            client_id);
        return false;
    }
    ++*nmsgs;

    // Send the final message
    msg.msg_type = MONAD_EVENT_MSG_EXPORT_FINISHED;
    mhdr.msg_control = nullptr;
    mhdr.msg_controllen = 0;
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&rss->mtx);
        close_fn(
            client,
            errno,
            "unable to send final message for client %u",
            client_id);
        return false;
    }
    ++*nmsgs;
    pthread_mutex_unlock(&rss->mtx);
    return true;
}

static bool export_recorder_ring(
    enum monad_event_ring_type ring_type,
    uint8_t const (*event_metadata_hash)[32], int sock_fd, unsigned client_id,
    close_client_err_fn *close_fn, struct monad_event_client *client, void *,
    unsigned *nmsgs)
{
    union
    {
        char buf[CMSG_SPACE(sizeof(int))];
        struct cmsghdr hdr;
    } cmsg;
    struct monad_event_export_success_msg msg;
    struct iovec msg_iov[1] = {[0] = {.iov_base = &msg, .iov_len = sizeof msg}};
    struct msghdr mhdr = {
        .msg_name = nullptr,
        .msg_namelen = 0,
        .msg_iov = msg_iov,
        .msg_iovlen = 1,
        .msg_control = cmsg.buf,
        .msg_controllen = sizeof cmsg,
        .msg_flags = 0};
    struct monad_event_recorder *const recorder =
        &g_monad_event_recorders[ring_type];

    if (memcmp(
            event_metadata_hash,
            g_monad_event_metadata_hash,
            sizeof g_monad_event_metadata_hash) != 0) {
        close_fn(
            client,
            EINVAL,
            "client %u metadata hash does not match server hash",
            client_id);
        return false;
    }

    cmsg.hdr.cmsg_level = SOL_SOCKET;
    cmsg.hdr.cmsg_type = SCM_RIGHTS;
    cmsg.hdr.cmsg_len = CMSG_LEN(sizeof(int));

    pthread_mutex_lock(&recorder->init_mtx);
    if (!atomic_load_explicit(&recorder->initialized, memory_order_acquire)) {
        pthread_mutex_unlock(&recorder->init_mtx);
        close_fn(
            client,
            ENOSYS,
            "event ring %hhu is not enabled in the server",
            ring_type);
        return false;
    }

    // Export the ring control file descriptor
    memset(&msg, 0, sizeof msg);
    msg.msg_type = MONAD_EVENT_MSG_MAP_RING_CONTROL;
    msg.ring_capacity = recorder->event_ring.capacity;
    *(int *)CMSG_DATA(&cmsg.hdr) = recorder->event_ring_fds.control_fd;

    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&recorder->init_mtx);
        close_fn(
            client,
            errno,
            "unable to export ring %hhu control fd to client %u",
            ring_type,
            client_id);
        return false;
    }
    ++*nmsgs;

    // Export the descriptor array file descriptor
    msg.msg_type = MONAD_EVENT_MSG_MAP_DESCRIPTOR_ARRAY;
    *(int *)CMSG_DATA(&cmsg.hdr) = recorder->event_ring_fds.descriptor_array_fd;

    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&recorder->init_mtx);
        close_fn(
            client,
            errno,
            "unable to export ring %hhu descriptor table fd to client %u",
            ring_type,
            client_id);
        return false;
    }
    ++*nmsgs;

    // Export the payload buffer file descriptor
    msg.msg_type = MONAD_EVENT_MSG_MAP_PAYLOAD_BUFFER;
    *(int *)CMSG_DATA(&cmsg.hdr) = recorder->event_ring_fds.payload_buf_fd;

    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&recorder->init_mtx);
        close_fn(
            client,
            errno,
            "unable to export ring %hhu payload buffer fd to client %u",
            ring_type,
            client_id);
        return false;
    }
    ++*nmsgs;

    // Send the final message
    msg.msg_type = MONAD_EVENT_MSG_EXPORT_FINISHED;
    mhdr.msg_control = nullptr;
    mhdr.msg_controllen = 0;
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        pthread_mutex_unlock(&recorder->init_mtx);
        close_fn(
            client,
            errno,
            "unable to send final message for ring %hhu to client %u",
            ring_type,
            client_id);
        return false;
    }
    ++*nmsgs;
    pthread_mutex_unlock(&recorder->init_mtx);
    return true;
}

static void send_heartbeat(void *)
{
    MONAD_EVENT(MONAD_EVENT_HEARTBEAT, 0);
}

static struct shared_mem_export_ops s_export_ops = {
    .cleanup = nullptr,
    .export_metadata = export_shared_recorder_metadata,
    .export_ring = export_recorder_ring,
    .send_heartbeat = send_heartbeat};

int monad_event_server_create(
    struct monad_event_server_options const *options,
    struct monad_event_server **server_p)
{
    return _monad_event_server_create_common(
        options, &s_export_ops, nullptr, server_p);
}
