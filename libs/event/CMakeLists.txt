project(monad_event)

# These files are shared by both the external clients and the event writer
# library (the "recorder") in libs/core
add_library(monad_event_core INTERFACE
    "src/monad/event/event.h"
    "src/monad/event/event_iterator.h"
    "src/monad/event/event_iterator_inline.h"
    "src/monad/event/event_types.h")

target_include_directories(monad_event_core INTERFACE "src")
target_compile_features(monad_event_core INTERFACE c_std_23)
