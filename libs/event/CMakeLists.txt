project(monad_event)

# These files are shared by both the external clients and the event writer
# library (the "recorder") in libs/core
add_library(monad_event_core STATIC
    "src/monad/event/event.h"
    "src/monad/event/event_iterator.h"
    "src/monad/event/event_iterator_inline.h"
    "src/monad/event/event_metadata.c"
    "src/monad/event/event_metadata.h"
    "src/monad/event/event_protocol.h")

target_include_directories(monad_event_core PUBLIC "src")
target_compile_features(monad_event_core PUBLIC c_std_23)
target_link_libraries(monad_event_core PUBLIC -latomic)

# This library allows external clients to import shared memory rings into their
# address space; it also links to the core library; it is meant to be shared with external clients, and should
# not link (or otherwise depend on) anything else in the execution repository
add_library(monad_event_client STATIC
    "src/monad/event/event_client.c"
    "src/monad/event/event_client.h")

target_compile_options(monad_event_client PRIVATE
    -Wall -Wextra -Wconversion -Werror)
target_link_libraries(monad_event_client PUBLIC monad_event_core)

option(MONAD_EVENT_BUILD_EXAMPLE
    "Build the example program that shows how to use the API" ON)

if (MONAD_EVENT_BUILD_EXAMPLE)
    add_executable(eventwatch "src/monad/event/example/eventwatch.c")
    target_link_libraries(eventwatch PRIVATE monad_event_client)
endif()

# Build a fake test server to connect to. This is off by default, because in
# the interest of code reuse it shares some code with the main execution
# repository, which we are not supposed to depend on. We break this rule
# here because this is only testing infrastructure: it is not needed to use
# the library, only to test the correctness of it.
option(MONAD_EVENT_BUILD_TEST_SERVER
    "Build a fake event server for running event client tests" OFF)

if (MONAD_EVENT_BUILD_TEST_SERVER)
    add_library(
        monad_event_test_server STATIC
        "../core/src/monad/core/assert.c"
        "../core/src/monad/event/event_server.c"
        "../core/src/monad/event/event_server.h"
        "../core/src/monad/event/event_shared.c"
        "../core/src/monad/event/event_shared.h"
        "src/monad/event/test/event_server_test.c")
    target_include_directories(monad_event_test_server PUBLIC "../core/src" "src")
    target_compile_definitions(monad_event_test_server PUBLIC "_GNU_SOURCE")
    target_link_libraries(monad_event_test_server PRIVATE monad_event_core)

    add_executable(event_test_server_driver "src/monad/event/test/driver.c")
    target_compile_features(event_test_server_driver PRIVATE c_std_23)
    target_link_libraries(event_test_server_driver PRIVATE monad_event_test_server)
endif()
