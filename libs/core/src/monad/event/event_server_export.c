/**
 * @file
 *
 * This file implements the OPEN_QUEUE message for the event server, when
 * it is exporting the shared memory segments of a queue populated by an event
 * recorder. This is in a separate file for a cleaner separation: this is the
 * only file that accesses the internals of both the event server and event
 * recorder.
 */

#include <string.h>

#include <errno.h>
#include <sys/socket.h>

#include <monad/core/spinlock.h>
#include <monad/event/event_metadata.h>
#include <monad/event/event_protocol.h>
#include <monad/event/event_recorder.h>

#include "event_server_internal.h"

static bool export_recorder_shared_memory_to_client(
    struct monad_event_open_queue_msg const *open_msg, int sock_fd,
    unsigned client_id, close_client_err_fn *close_fn,
    struct monad_event_client *client, void *, unsigned *nmsgs)
{
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
    char page_name[32];
    struct monad_event_recorder *const recorder =
        &g_monad_event_recorders[open_msg->queue_type];

    if (memcmp(
            open_msg->event_metadata_hash,
            g_monad_event_metadata_hash,
            sizeof g_monad_event_metadata_hash) != 0) {
        close_fn(
            client, EINVAL, "client metadata hash does not match server hash");
        return false;
    }

    // To understand the flow of this function, see the comment for the client
    // side in the `open_queue` function (event_queue.c)
    cmsg.hdr.cmsg_level = SOL_SOCKET;
    cmsg.hdr.cmsg_type = SCM_RIGHTS;
    cmsg.hdr.cmsg_len = CMSG_LEN(sizeof(int));

    MONAD_SPINLOCK_LOCK(&recorder->lock);
    if (!atomic_load_explicit(&recorder->initialized, memory_order_acquire)) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            ENOSYS,
            "event queue %hhu is not enabled in the server",
            open_msg->queue_type);
        return false;
    }

    // Export the ring control file descriptor
    memset(&msg, 0, sizeof msg);
    msg.msg_type = MONAD_EVENT_MSG_MAP_RING_CONTROL;
    msg.ring_capacity = recorder->event_ring.capacity;
    msg.payload_page_pool_size = (uint16_t)recorder->all_pages_size;
    msg.cur_seqno = atomic_load_explicit(
        &recorder->event_ring.control->prod_next, memory_order_acquire);
    *(int *)CMSG_DATA(&cmsg.hdr) = recorder->event_ring.control_fd;

    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to export ring control fd for queue %u:%hhu",
            client_id,
            open_msg->queue_type);
        return false;
    }
    ++*nmsgs;

    // Export the descriptor table file descriptor
    msg.msg_type = MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE;
    *(int *)CMSG_DATA(&cmsg.hdr) = recorder->event_ring.descriptor_table_fd;

    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to export descriptor table fd %u:%hhu",
            client_id,
            open_msg->queue_type);
        return false;
    }
    ++*nmsgs;

    // Export all payload page file descriptors
    msg.msg_type = MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE;
    MONAD_SPINLOCK_LOCK(&recorder->payload_page_pool.lock);
    for (size_t p = 0; p < recorder->all_pages_size; ++p) {
        msg.page_id = recorder->all_pages[p]->page_id;
        *(int *)CMSG_DATA(&cmsg.hdr) = recorder->all_pages[p]->memfd;
        if (sendmsg(sock_fd, &mhdr, 0) == -1) {
            // Copy the diagnostic name before unlocking the page
            strncpy(
                page_name, recorder->all_pages[p]->page_name, sizeof page_name);
            MONAD_SPINLOCK_UNLOCK(&recorder->payload_page_pool.lock);
            MONAD_SPINLOCK_UNLOCK(&recorder->lock);
            close_fn(
                client,
                errno,
                "unable to export event page %s for queue %u:%hhu",
                page_name,
                client_id,
                open_msg->queue_type);
            return false;
        }
        ++*nmsgs;
    }
    MONAD_SPINLOCK_UNLOCK(&recorder->payload_page_pool.lock);

    // Send the thread table metadata message
    msg.msg_type = MONAD_EVENT_MSG_METADATA_OFFSET;
    msg.metadata_type = MONAD_EVENT_METADATA_THREAD;
    monad_event_recorder_export_metadata_section(
        msg.metadata_type, &msg.page_id, &msg.metadata_offset);
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to send thread offset table message %u:%hhu",
            client_id,
            open_msg->queue_type);
        return false;
    }
    ++*nmsgs;

    // Send the block info table metadata message
    msg.metadata_type = MONAD_EVENT_METADATA_BLOCK_FLOW;
    monad_event_recorder_export_metadata_section(
        msg.metadata_type, &msg.page_id, &msg.metadata_offset);
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to send block flow offset table message %u:%hhu",
            client_id,
            open_msg->queue_type);
        return false;
    }
    ++*nmsgs;

    // Send the final message
    msg.msg_type = MONAD_EVENT_MSG_OPEN_FINISHED;
    mhdr.msg_control = nullptr;
    mhdr.msg_controllen = 0;
    if (sendmsg(sock_fd, &mhdr, 0) == -1) {
        MONAD_SPINLOCK_UNLOCK(&recorder->lock);
        close_fn(
            client,
            errno,
            "unable to send final message for queue %u:%hhu",
            client_id,
            open_msg->queue_type);
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
    .export = export_recorder_shared_memory_to_client,
    .heartbeat = heartbeat};

int monad_event_server_create(
    struct monad_event_server_options const *options,
    struct monad_event_server **server_p)
{
    return _monad_event_server_create_common(
        options, &s_export_ops, nullptr, server_p);
}
