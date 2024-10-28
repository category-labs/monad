#pragma once

/**
 * @file
 *
 * This file defines the structures that are passed over the UNIX domain
 * socket between the event server and event clients. The purpose of this
 * protocol is to set up the shared memory structures for an event queue
 * in both processes, and to control the event queue's domain enable mask.
 */

#include <stdint.h>

enum monad_event_msg_type : unsigned
{
    MONAD_EVENT_MSG_NONE,

    // Client -> server messages
    MONAD_EVENT_MSG_OPEN_SESSION,
    MONAD_EVENT_MSG_SET_DOMAIN_MASK,

    // Server -> client messages
    MONAD_EVENT_MSG_SESSION_ERROR,
    MONAD_EVENT_MSG_MAP_RING_CONTROL,
    MONAD_EVENT_MSG_MAP_DESCRIPTOR_TABLE,
    MONAD_EVENT_MSG_MAP_PAYLOAD_PAGE,
    MONAD_EVENT_MSG_SESSION_OPEN,
    MONAD_EVENT_MSG_NEW_DOMAIN_MASK
};

struct monad_event_open_session_msg
{
    enum monad_event_msg_type msg_type;
    uint8_t ring_shift;
    size_t domain_count;

    struct monad_event_client_domain_info
    {
        uint8_t domain_code;
        uint8_t domain_metadata_hash[32];
    } domain_info[];
};

struct monad_event_set_domain_mask_msg
{
    enum monad_event_msg_type msg_type;
    uint64_t domain_mask;
};

/// Any request from the client that fails is answered with this message
struct monad_event_session_error_msg
{
    enum monad_event_msg_type msg_type;
    uint32_t session_id;
    int error_code;
    char error_buf[512];
};

/// All "success" responses from the server re-use this same structure, so
/// some fields will not be relevant for every message type
struct monad_event_session_success_msg
{
    enum monad_event_msg_type msg_type;
    uint32_t session_id;
    size_t ring_capacity;
    uint64_t recorder_domain_mask;
    uint64_t effective_domain_mask;
};
