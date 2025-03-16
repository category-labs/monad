cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad-runloop LANGUAGES C CXX ASM)

find_package(GTest REQUIRED)
find_program(BINDGEN_PROGRAM bindgen)
find_program(RUSTC_PROGRAM rustc)

add_subdirectory("third_party/monad-boost-context")

add_library(monad_context_c-custom-binutils-gdb INTERFACE IMPORTED)
target_include_directories(monad_context_c-custom-binutils-gdb INTERFACE "third_party/binutils-gdb")

set(monad_context_INCLUDES
  "src/monad/context/context_switcher.h"
)
add_library(monad_context_c STATIC
  "src/monad/context/context_switcher_none.c"
  "src/monad/context/context_switcher_fcontext.c"
  "src/monad/context/context_switcher_sjlj.c"
)
monad_compile_options(monad_context_c)
target_compile_options(monad_context_c PRIVATE -Wpedantic)
target_compile_definitions(monad_context_c PRIVATE MONAD_CONTEXT_SOURCE=1)
target_include_directories(monad_context_c PUBLIC "src")
target_link_libraries(monad_context_c PRIVATE monad_boost_context monad_core monad_context_c-custom-binutils-gdb)

# This MUST be a shared library called libthread_db.so for GDB to load it
# We do NOT use monad_compile_options() here because this custom libthread_db.so.1
# is loaded as a plugin into GDB, and by rights should be compiled with whatever
# GDB is. The current implementation is "lucky" in that it doesn't cause the loading
# of anything which would blow up GDB, but if say any C++ ever appeared in the
# source code to cause an incompatible libstdc++ to get loaded, very bad.
add_library(monad_context_c_libthread_db SHARED
  "src/monad/context/thread_db.c"
)
target_compile_features(monad_context_c_libthread_db PRIVATE c_std_23 cxx_std_20)
target_compile_options(monad_context_c_libthread_db PRIVATE -Wall -Wextra -Wconversion -Werror)
# Hide all symbols in this except those explicitly made visibile to prevent
# unhelpful collision with the GDB process symbols
target_compile_options(monad_context_c_libthread_db PRIVATE -fvisibility=hidden)
# Because GDB loads libthread_db.so, if we compile it with a sanitiser, the
# sanitiser will blow up as it needs GDB to have sanitiser enabled too. So
# prevent our toolchain having effects here.
target_compile_options(monad_context_c_libthread_db PRIVATE -fno-sanitize=all)
target_link_options(monad_context_c_libthread_db PRIVATE -fno-sanitize=all)
set_target_properties(monad_context_c_libthread_db PROPERTIES
  POSITION_INDEPENDENT_CODE ON
  OUTPUT_NAME "thread_db"
  SUFFIX ".so.1"
)
target_link_libraries(monad_context_c_libthread_db PRIVATE monad_context_c-custom-binutils-gdb)
# We need to inhibit all dependencies on anything else to prevent clashing with GDB's runtime
# when loaded in as a plugin. TODO FIXME this is failing to link. If it does ever cause
# problems with GDB, diagnosing and fixing this should be revisited.
#target_link_options(monad_context_c_libthread_db PRIVATE -static)
target_compile_definitions(monad_context_c PUBLIC MONAD_CONTEXT_CUSTOM_GDB_THREAD_DB_PATH=$<TARGET_FILE_DIR:monad_context_c_libthread_db>)

set(monad_async_INCLUDES
  "src/monad/async/executor.h"
  "src/monad/async/file_io.h"
  "src/monad/async/socket_io.h"
  "src/monad/async/task.h"
  "src/monad/async/util.h"
  "src/monad/async/work_dispatcher.h"
)
add_library(monad_async_c STATIC
  "src/monad/async/executor.c"
  "src/monad/async/file_io.c"
  "src/monad/async/socket_io.c"
  "src/monad/async/task.c"
  "src/monad/async/util.cpp"
  "src/monad/async/work_dispatcher.c"
)
monad_compile_options(monad_async_c)
target_compile_options(monad_async_c PRIVATE -Wpedantic)
target_compile_definitions(monad_async_c PRIVATE MONAD_ASYNC_SOURCE=1)
target_include_directories(monad_async_c PUBLIC "src")
target_link_libraries(monad_async_c PUBLIC uring monad_core monad_context_c)

# This is reasonable behavior to have, that is not strictly needed at the
# moment for `monad` but could cause surprises later and failures in the test
# suite. This should be the normal behavior (without a configuration option)
# if we can figure out how to avoid the slight performance hit
option(MONAD_FIBER_RUN_QUEUE_SUPPORT_EQUAL_PRIO
        "Allow the run_queue to support equal priority fibers" ON)

set(monad_fiber_c_INCLUDES
  "src/monad/fiber/fiber.h"
  "src/monad/fiber/fiber_channel.h"
  "src/monad/fiber/fiber_inline.h"
  "src/monad/fiber/fiber_semaphore.h"
  "src/monad/fiber/run_queue.h")
add_library(monad_fiber_c STATIC
  "src/monad/fiber/fiber.c"
  "src/monad/fiber/fiber_thr.c"
  "src/monad/fiber/run_queue.c")
if (MONAD_FIBER_RUN_QUEUE_SUPPORT_EQUAL_PRIO)
    target_compile_definitions(monad_fiber_c
            PUBLIC MONAD_FIBER_RUN_QUEUE_SUPPORT_EQUAL_PRIO)
endif()
monad_compile_options(monad_fiber_c)
target_include_directories(monad_fiber_c PUBLIC "src")
target_link_libraries(monad_fiber_c PUBLIC monad_core monad_boost_context)

set(monad_fiber_INCLUDES
  "src/monad/fiber/config.hpp"
  "src/monad/fiber/priority_pool.hpp"
  "src/monad/fiber/priority_task.hpp")

add_library(monad_fiber STATIC
  "src/monad/fiber/priority_pool.cpp")
monad_compile_options(monad_fiber PUBLIC cxx_std_23)
target_include_directories(monad_fiber PUBLIC "src")
target_link_libraries(monad_fiber PUBLIC monad_fiber_c monad_core)

if(BINDGEN_PROGRAM)
  add_custom_command(OUTPUT "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs"
    COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/monad/async/all.h"
    --allowlist-function "monad_async.*"
    --allowlist-function "monad_c_.*"
    --allowlist-function "monad_context.*"
    --allowlist-type "monad_async.*"
    --allowlist-type "monad_c_.*"
    --allowlist-type "monad_context.*"
    --allowlist-var "monad_async.*"
    --allowlist-var "monad_c_.*"
    --allowlist-var "monad_context.*"
    --generate-inline-functions
    --no-layout-tests
    --no-copy "monad_async.*"
    --no-copy "monad_c_.*"
    --no-copy "monad_context.*"
    --with-derive-default
    --must-use-type cxx_status_code_system
    --must-use-type cxx_result_status_code_system_monad_async
    --
    -I ${CMAKE_CURRENT_LIST_DIR}/src
    -I ${monad_core_SOURCE_DIR}/src
    -D _GNU_SOURCE
    -D MONAD_CONTEXT_DISABLE_INLINE_CUSTOM_GDB_THREAD_DB_LOAD
    -std=c23
    DEPENDS ${monad_async_INCLUDES} ${monad_context_INCLUDES}
  )
  add_custom_target(monad_async_c_regenerate_rust_bindings DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs")
  add_dependencies(monad_async_c monad_async_c_regenerate_rust_bindings)
else()
  message(WARNING "WARNING: Could not regen Rust bindings as bindgen program not found")
endif()

enable_testing()

add_subdirectory("src/monad/async/test")
add_subdirectory("src/monad/context/test")
add_subdirectory("src/monad/fiber/test")

if(RUSTC_PROGRAM AND NOT CMAKE_C_FLAGS_INIT MATCHES "fsanitize=")
    cmake_host_system_information(RESULT linux_flavour QUERY DISTRIB_ID)
    if(linux_flavour MATCHES "debian|ubuntu")
        find_package(Boost REQUIRED stacktrace_backtrace)
        add_library(boost_stacktrace_backtrace ALIAS Boost::stacktrace_backtrace)
        set(BOOST_STACKTRACE_LIB boost_stacktrace_backtrace)
    else()
        find_package(Boost REQUIRED stacktrace_addr2line)
        add_library(boost_stacktrace_addr2line ALIAS Boost::stacktrace_addr2line)
        set(BOOST_STACKTRACE_LIB boost_stacktrace_addr2line)
    endif()

    add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/test/rust_tests"
    COMMAND "${RUSTC_PROGRAM}" --test -o "${CMAKE_BINARY_DIR}/test/rust_tests"
    "${CMAKE_CURRENT_SOURCE_DIR}/rust/test.rs"
    -L "$<TARGET_FILE_DIR:monad_async_c>"
    -L "$<TARGET_FILE_DIR:monad_context_c>"
    -L "$<TARGET_FILE_DIR:monad_core>"
    -l $<TARGET_NAME:monad_async_c>
    -l $<TARGET_NAME:monad_context_c>
    -l $<TARGET_NAME:monad_core>
    -L "$<TARGET_FILE_DIR:${BOOST_STACKTRACE_LIB}>"
    -l $<TARGET_NAME:${BOOST_STACKTRACE_LIB}>
    -l stdc++
    -l uring
    DEPENDS
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/async_with_rust_helpers.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/test.rs"
      "${CMAKE_CURRENT_SOURCE_DIR}/rust/async.rs"
  )
  add_custom_target(monad_async_c_rust_tests ALL DEPENDS "${CMAKE_BINARY_DIR}/test/rust_tests")
  add_dependencies(monad_async_c_rust_tests monad_async_c monad_context_c)
  add_test(NAME monad_async_c_rust_tests COMMAND "${CMAKE_BINARY_DIR}/test/rust_tests" --nocapture)
endif()
