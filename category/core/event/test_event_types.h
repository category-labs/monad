#pragma once

/**
 * @file
 *
 * Definitions of events used with the TEST event ring
 */

#include <stdint.h>

#include <category/core/event/event_metadata.h>

#ifdef __cplusplus
extern "C"
{
#endif

/// Each type of event is assigned a unique value in this enumeration
enum monad_test_event : uint16_t
{
    MONAD_TEST_EVENT_NONE,
    MONAD_TEST_EVENT_COUNTER,
};

/// Event payload for MONAD_TEST_EVENT_COUNTER
struct monad_test_event_counter
{
    uint8_t writer_id;
    uint64_t counter;
};

extern struct monad_event_metadata const g_monad_test_event_metadata[2];
extern uint8_t const g_monad_test_event_metadata_hash[32];

#define MONAD_EVENT_DEFAULT_TEST_RING_PATH "/dev/hugepages/event-recorder-test"

#ifdef __cplusplus
} // extern "C"
#endif
