/**
 * @file
 *
 * This file implements the EXPORT_RING message for the event server, when
 * it is exporting the shared memory segments of an event ring populated by the
 * libs/core recorder. This is in a separate file for a cleaner separation:
 * this is the only file that accesses the internals of both the event server
 * and event recorder.
 */

#include <string.h>

#include <errno.h>
#include <sys/socket.h>

#include <monad/core/spinlock.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_recorder.h>

#include "event_server_internal.h"

/*
 * To understand the flow of the export process, see the comments for the
 * client side (event_client.c in the libs/event library)
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

    MONAD_SPINLOCK_LOCK(&rss->lock);
    // Send the metadata payload page
    msg.msg_type = MONAD_EVENT_MSG_MAP_METADATA_PAGE;
    *(int *)CMSG_DATA(&cmsg.hdr) = rss->metadata_page.memfd;
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        // Copy the diagnostic name before unlocking the page
        MONAD_SPINLOCK_UNLOCK(&rss->lock);
        close_fn(
            client,
            errno,
            "unable to export metadata page for ring to client %u",
            client_id);
        return false;
    }
    ++*nmsgs;

    // Send the thread table metadata message
    msg.msg_type = MONAD_EVENT_MSG_METADATA_OFFSET;
    msg.metadata_type = MONAD_EVENT_METADATA_THREAD;
    monad_event_recorder_export_metadata_section(
        msg.metadata_type, &msg.metadata_offset);
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&rss->lock);
        close_fn(
            client,
            errno,
            "unable to send thread offset table message to client %u",
            client_id);
        return false;
    }
    ++*nmsgs;

    // Send the block info table metadata message
    msg.metadata_type = MONAD_EVENT_METADATA_BLOCK_FLOW;
    monad_event_recorder_export_metadata_section(
        msg.metadata_type, &msg.metadata_offset);
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&rss->lock);
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
        MONAD_SPINLOCK_UNLOCK(&rss->lock);
        close_fn(
            client,
            errno,
            "unable to send final message for client %u",
            client_id);
        return false;
    }
    ++*nmsgs;
    MONAD_SPINLOCK_UNLOCK(&rss->lock);
    return true;
}

static bool export_recorder_ring(
    struct monad_event_export_ring_msg const *export_msg, int sock_fd,
    unsigned client_id, close_client_err_fn *close_fn,
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
    struct monad_event_recorder *const recorder =
        &g_monad_event_recorders[export_msg->ring_type];

    if (memcmp(
            export_msg->event_metadata_hash,
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

    MONAD_SPINLOCK_LOCK(&recorder->lock);
    if (!atomic_load_explicit(&recorder->initialized, memory_order_acquire)) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            ENOSYS,
            "event ring %hhu is not enabled in the server",
            export_msg->ring_type);
        return false;
    }

    // Export the ring control file descriptor
    memset(&msg, 0, sizeof msg);
    msg.msg_type = MONAD_EVENT_MSG_MAP_RING_CONTROL;
    *(int *)CMSG_DATA(&cmsg.hdr) = recorder->control_fd;

    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to export ring %hhu control fd to client %u",
            export_msg->ring_type,
            client_id);
        return false;
    }
    ++*nmsgs;

    // Export the FIFO buffer file descriptor
    msg.msg_type = MONAD_EVENT_MSG_MAP_RING_FIFO;
    *(int *)CMSG_DATA(&cmsg.hdr) = recorder->fifo_fd;

    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to export ring %hhu FIFO buffer fd to client %u",
            export_msg->ring_type,
            client_id);
        return false;
    }
    ++*nmsgs;

    // Send the final message
    msg.msg_type = MONAD_EVENT_MSG_EXPORT_FINISHED;
    mhdr.msg_control = nullptr;
    mhdr.msg_controllen = 0;
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to send final message for ring %hhu to client %u",
            export_msg->ring_type,
            client_id);
        return false;
    }
    ++*nmsgs;
    MONAD_SPINLOCK_UNLOCK(&recorder->lock);
    return true;
}

static void heartbeat(void *)
{
    MONAD_EVENT(MONAD_EVENT_HEARTBEAT, 0);
}

static struct shared_mem_export_ops s_export_ops = {
    .cleanup = nullptr,
    .export_metadata = export_shared_recorder_metadata,
    .export_ring = export_recorder_ring,
    .heartbeat = heartbeat};

int monad_event_server_create(
    struct monad_event_server_options const *options,
    struct monad_event_server **server_p)
{
    return _monad_event_server_create_common(
        options, &s_export_ops, nullptr, server_p);
}
