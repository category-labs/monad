#pragma once

/**
 * @file
 *
 * Core definitions of event enumeration types and event payload structures
 */

#include <stdint.h>

// clang-format off
#ifdef __cplusplus

extern "C"
{
#endif

/// Each type of event is assigned a unique value in this enumeration
enum monad_event_type : uint16_t
{
    MONAD_EVENT_NONE,
    MONAD_EVENT_TEST_COUNTER,
};

/// Event payload for MONAD_EVENT_TEST_COUNTER
struct monad_event_test_counter
{
    uint8_t writer_id;
    uint64_t counter;
};

#ifdef __cplusplus
} // extern "C"

// clang-format on
#endif
