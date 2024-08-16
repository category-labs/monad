cmake_minimum_required(VERSION 3.5)

project(monad-runloop LANGUAGES C CXX ASM)

find_package(GTest REQUIRED)
find_program(BINDGEN_PROGRAM bindgen)
find_program(RUSTC_PROGRAM rustc)

add_subdirectory("third_party/monad-boost-context")

set(monad_context_INCLUDES
  "src/monad/context/context_switcher.h"
)
add_library(monad_context_c STATIC
  "src/monad/context/context_switcher_none.c"
  "src/monad/context/context_switcher_fcontext.c"
  "src/monad/context/context_switcher_sjlj.c"
)
target_compile_features(monad_context_c PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_context_c PRIVATE -Wall -Wextra -Wconversion -Wpedantic -Werror)
target_compile_definitions(monad_context_c PRIVATE _GNU_SOURCE=1 MONAD_CONTEXT_SOURCE=1)
target_include_directories(monad_context_c PUBLIC "src")
target_link_libraries(monad_context_c PUBLIC monad_boost_context)
monad_target_gdb_pretty_printer(monad_context_c monad_context_c_pretty_printer "src/monad/context/gdb_pretty_printers.py")

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
target_compile_features(monad_async_c PUBLIC c_std_23 cxx_std_20)
target_compile_options(monad_async_c PRIVATE -Wall -Wextra -Wconversion -Wpedantic -Werror)
target_compile_definitions(monad_async_c PRIVATE MONAD_ASYNC_SOURCE=1)
target_include_directories(monad_async_c PUBLIC "src")
target_link_libraries(monad_async_c PUBLIC uring monad_core monad_context_c)

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
    --must-use-type cxx_result_status_code_system_monad_async
    --
    -I ${CMAKE_CURRENT_LIST_DIR}/src
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
