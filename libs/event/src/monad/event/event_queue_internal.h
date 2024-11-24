#pragma once

/**
 * @file
 *
 * This file contains some implementation details which in principle should be
 * private to event_queue.c, but the testing code benefits if we share them in
 * a limited way. Third-party users should not include this file or rely on the
 * layout of `monad_event_queue` in any way.
 */

#include <monad/event/event.h>
#include <stdint.h>

// clang-format off

struct monad_event_queue
{
    int sock_fd;                         ///< PF_LOCAL sock connected to server
    uint16_t num_payload_pages;          ///< Size of `payload_pages` array
    enum monad_event_queue_type type;    ///< What kind of queue this is
    struct monad_event_payload_page const
        **payload_pages;                 ///< Array of shared mem payload pages
    struct monad_event_ring event_ring;  ///< Shared mem event descriptor ring
};

// clang-format on
