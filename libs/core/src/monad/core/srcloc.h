#pragma once

typedef struct monad_source_location monad_source_location_t;

/// A pure C structure similar to C++20's std::source_location
struct monad_source_location
{
    char const *function_name;
    char const *file_name;
    unsigned line;
    unsigned column;
};

/// Creates a compound literal of the current source location for use in a
/// macro, similar to the C++20 consteval std::source_location::current()
#define MONAD_SOURCE_LOCATION_CURRENT()                                        \
    ((monad_source_location_t){__PRETTY_FUNCTION__, __FILE__, __LINE__, 0})
