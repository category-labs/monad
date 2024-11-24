#pragma once

/**
 * @file
 *
 * This file, along with event_metadata.c, provide access to metadata about
 * events that live in the object file's static data section and are
 * efficient to access.
 */

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

enum monad_event_type : uint16_t;

// clang-format off

/// Metadata describing each event in an event domain
struct monad_event_metadata
{
    enum monad_event_type type;  ///< Enumeration constant
    char const *c_name;          ///< Short form C style name
    char const *description;     ///< Text description for UI cmds
};

// clang-format on

/// Metadata of all currently understood events, as global static data
extern struct monad_event_metadata const g_monad_event_metadata[];

/// Size of the g_monad_event_metadata array
extern size_t const g_monad_event_metadata_size;

/// SHA-256 hash of the all parts of the event metadata that affect
/// binary compatibility
extern uint8_t const g_monad_event_metadata_hash[32];

#ifdef __cplusplus
} // extern "C"
#endif
