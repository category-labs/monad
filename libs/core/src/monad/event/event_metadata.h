#pragma once

#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

// clang-format off

/// Metadata describing each event in an event domain
struct monad_event_metadata
{
    uint16_t event_type;      ///< Enumeration constant
    char const *c_name;       ///< Short form C style name
    char const *description;  ///< Text description for UI commands
};

// clang-format on

#ifdef __cplusplus
} // extern "C"
#endif
