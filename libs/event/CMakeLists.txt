project(monad_event)

# These files are shared by both the external clients and the event writer
# library (the "recorder") in libs/core
add_library(monad_event STATIC
    "src/monad/event/event.h"
    "src/monad/event/event_error.c"
    "src/monad/event/event_error.h"
    "src/monad/event/event_iterator.h"
    "src/monad/event/event_iterator_inline.h"
    "src/monad/event/event_metadata.c"
    "src/monad/event/event_metadata.h"
    "src/monad/event/event_ring_db.c"
    "src/monad/event/event_ring_db.h")

target_include_directories(monad_event PUBLIC "src")
target_compile_features(monad_event PUBLIC c_std_23)
target_compile_options(monad_event PRIVATE -Wall -Wextra -Wconversion -Werror)

option(MONAD_EVENT_BUILD_EXAMPLE
    "Build the example program that shows how to use the API" ON)

if (MONAD_EVENT_BUILD_EXAMPLE)
    add_executable(eventwatch "src/monad/event/example/eventwatch.c")
    target_link_libraries(eventwatch PRIVATE monad_event)
endif()

add_library(monad_event_test_util
    "src/monad/event/event_test_util.c"
    "src/monad/event/event_test_util.h")
target_compile_options(monad_event_test_util PRIVATE -Wall -Wextra -Wconversion -Werror)
target_link_libraries(monad_event_test_util PUBLIC monad_event -lzstd)
