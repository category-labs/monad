# This cmake project can be used to build the client part of the monad event
# library without building all of libmonad_core.a or using the rest of the CMake
# build system, i.e., this can be used a top-level source directory to just
# build these components. This is useful for external third-party clients, and
# for the Rust build system.

project(monad_event)

add_library(
  monad_event STATIC
  "../core/format_err.c"
  "../core/format_err.h"
  "../core/srcloc.h"
  "../core/event/event_iterator.h"
  "../core/event/event_iterator_inline.h"
  "../core/event/event_metadata.h"
  "../core/event/event_ring.c"
  "../core/event/event_ring.h"
  "../core/event/event_ring_util.c"
  "../core/event/event_ring_util.h"
  "../execution/ethereum/core/base_ctypes.h"
  "../execution/ethereum/core/eth_ctypes.h"
  "../execution/ethereum/event/exec_event_ctypes.h"
  "../execution/ethereum/event/exec_event_ctypes_metadata.c"
  "../execution/ethereum/event/exec_iter_help.h")

target_include_directories(monad_event PUBLIC "../..")
target_compile_definitions(monad_event PUBLIC _GNU_SOURCE)
target_compile_features(monad_event PUBLIC c_std_23)
target_compile_options(monad_event PRIVATE -Wall -Wextra -Wconversion -Werror)

option(MONAD_EVENT_BUILD_EXAMPLE
    "Build the example program that shows how to use the API" ON)

if (MONAD_EVENT_BUILD_EXAMPLE)
    add_executable(eventwatch "example/eventwatch.c")
    target_link_libraries(eventwatch PRIVATE monad_event)
endif()
