#pragma once

/**
 * @file
 *
 * This file, along with event_metadata.c, turns the event definitions
 * into metadata structures using the C preprocessor. These live in the
 * object file's static data section and are efficient to access.
 */

#include <stddef.h>
#include <stdint.h>

#include <monad/event/event.h>

#ifdef __cplusplus
extern "C"
{
#endif

// clang-format off

enum monad_event_trace_flags : uint8_t
{
    MONAD_EVENT_TRACE_DEFAULT = 0,
    MONAD_EVENT_TRACE_PUSH_SCOPE = 0b1
};

/// Metadata describing each event in an event domain
struct monad_event_metadata
{
    enum monad_event_type type;        ///< Enumeration constant
    uint8_t trace_flags;               ///< Trace flags from .def file
    char const *c_symbol;              ///< Identifier of C enum constant
    char const *c_name;                ///< Short form C style name
    char const *camel_name;            ///< UI-friendly camel-case name
    char const *description;           ///< Text description for UI cmds
};

/// Metadata describing each domain in the tracer
struct monad_event_domain_metadata
{
    enum monad_event_domain domain;    ///< Enumeration constant
    char const *name;                  ///< Human-friendly name of domain
    char const *description;           ///< Text description for UI programs
    struct monad_event_metadata const *
        event_meta;                    ///< Array of domain's event metadata
    size_t num_events;                 ///< Size of `event_meta` array
};

// clang-format on

/// Metadata of all currently understood domains, as global static data
extern struct monad_event_domain_metadata const g_monad_event_domain_meta[];

/// Size of the g_monad_event_domain_meta array
extern size_t const g_monad_event_domain_meta_size;

/// Serialize domain metadata to a buffer. Although users typically want the
/// static table of metadata (in `g_monad_event_domain_meta`), this function
/// can be used to check if event definitions across different processes
/// match each other, usually by comparing hashed values of serialized metadata.
/// The caller is responsible for calling free(3) on `meta_buf`
int monad_event_metadata_serialize(
    struct monad_event_domain_metadata const *, char **meta_buf,
    size_t *meta_buf_size);

/// Deserialization counterpart to monad_event_metadata_serialize. This assumes
/// that `buf` is stable: the C strings will be set up to point inside `buf`.
int monad_event_metadata_deserialize(
    char const *buf, size_t buf_size, struct monad_event_domain_metadata *,
    int (*event_alloc_fn)(struct monad_event_domain_metadata *, void *),
    void *alloc_param);

/// Given the canonical (all lowercase) string name of a domain, look up the
/// associated metadata structure for it
struct monad_event_domain_metadata const *
monad_event_metadata_lookup(char const *);

/// Parse an input string into a domain mask. The string may be a numerical
/// mask (starting with 0 or 0x if it is expressed as octal or hexadecimal) or
/// a comma-separated list of domain names. It also recognizes the special
/// names "all" and "none".
int monad_event_parse_domain_mask(char const *input, uint64_t *mask);

#ifdef __cplusplus
} // extern "C"
#endif
