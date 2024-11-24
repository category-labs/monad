#pragma once

/**
 * @file
 *
 * This file defines the structures that are passed over the UNIX domain
 * socket between the event server and event clients. The purpose of this
 * protocol is to set up the shared memory structures for an event queue
 * in both processes.
 */

#include <stddef.h>
#include <stdint.h>

enum monad_event_queue_type : uint8_t;

enum monad_event_metadata_type : uint8_t
{
    MONAD_EVENT_METADATA_NONE, ///< Not a valid metadata type
    MONAD_EVENT_METADATA_THREAD, ///< monad_event_thread_info[] in shmem
    MONAD_EVENT_METADATA_BLOCK_FLOW ///< monad_event_block_flow_info[] in shmem
};

enum monad_event_msg_type : unsigned
{
    MONAD_EVENT_MSG_NONE,

    // Client -> server messages
    MONAD_EVENT_MSG_OPEN_QUEUE,

    // Server -> client messages
    MONAD_EVENT_MSG_OPEN_ERROR,
    MONAD_EVENT_MSG_MAP_RING_CONTROL,
    MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE,
    MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE,
    MONAD_EVENT_MSG_METADATA_OFFSET,
    MONAD_EVENT_MSG_OPEN_FINISHED
};

/// Message sent from client for msg_type == MONAD_EVENT_MSG_OPEN_QUEUE
struct monad_event_open_queue_msg
{
    enum monad_event_msg_type msg_type;
    enum monad_event_queue_type queue_type;
    uint8_t event_metadata_hash[32];
};

/// Message sent from server for msg_type == MONAD_EVENT_MSG_OPEN_ERROR; any
/// request from the client that fails is answered with this message
struct monad_event_open_error_msg
{
    enum monad_event_msg_type msg_type;
    int error_code;
    char error_buf[512];
};

/// All "success" responses from the server re-use this same structure, but
/// with different msg_type values; not all fields are meaningful for each type
struct monad_event_open_success_msg
{
    enum monad_event_msg_type msg_type;
    enum monad_event_metadata_type metadata_type;
    uint32_t metadata_offset;
    uint16_t page_id;
    uint16_t payload_page_pool_size;
    size_t ring_capacity;
    uint64_t cur_seqno;
};
