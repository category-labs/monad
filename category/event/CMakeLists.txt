# This cmake project can be used to build the client part of the monad event
# library without building all of libmonad_core.a or using the rest of the
# CMake build system, i.e., this can be used a top-level source directory to
# just build these components. This is useful for external third-party
# clients, and for the Rust build system.

project(monad_event)

add_library(monad_event STATIC
    "../core/src/monad/core/format_err.c"
    "../core/src/monad/core/format_err.h"
    "../core/src/monad/core/srcloc.h"
    "../core/src/monad/event/event_iterator.h"
    "../core/src/monad/event/event_iterator_inline.h"
    "../core/src/monad/event/event_metadata.h"
    "../core/src/monad/event/event_ring.c"
    "../core/src/monad/event/event_ring.h"
    "../core/src/monad/event/event_ring_util.c"
    "../core/src/monad/event/event_ring_util.h")

target_include_directories(monad_event PUBLIC "../core/src")
target_compile_definitions(monad_event PUBLIC _GNU_SOURCE)
target_compile_features(monad_event PUBLIC c_std_23)
target_compile_options(monad_event PRIVATE -Wall -Wextra -Wconversion -Werror)
