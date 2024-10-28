project(monad_event)

# These header files are shared by both the consumer library and the
# event producer in libs/core
add_library(monad_event_core STATIC
    "src/monad/event/event.h"
    "src/monad/event/event_metadata.c"
    "src/monad/event/event_metadata.h"
    "src/monad/event/event_protocol.h"
    "src/monad/event/event_shmem.h")

target_include_directories(monad_event_core PUBLIC "src")
target_compile_features(monad_event_core PUBLIC c_std_23)

# This is the consumer library for the event system; it is meant to be
# shared with external clients, and should not link (or otherwise depend on)
# anything from monad
add_library(monad_event_consumer STATIC
    "src/monad/event/event_consumer.c"
    "src/monad/event/event_consumer.h"
    "../core/third_party/openssl/crypto/sha/keccak1600.c")

target_compile_definitions(monad_event_consumer PRIVATE "_GNU_SOURCE")
target_compile_options(monad_event_consumer PRIVATE
    -Wall -Wextra -Wconversion -Werror)
target_link_libraries(monad_event_consumer PUBLIC monad_event_core)
