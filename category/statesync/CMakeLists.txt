cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad_statesync)

add_library(
  monad_statesync
  OBJECT
  # server
  "statesync_client.cpp"
  "statesync_client.h"
  "statesync_client_context.cpp"
  "statesync_client_context.hpp"
  "statesync_messages.h"
  "statesync_protocol.hpp"
  "statesync_protocol.cpp"
  "statesync_server.cpp"
  "statesync_server.h"
  "statesync_server_context.cpp"
  "statesync_server_context.hpp"
  "statesync_server_context.hpp"
  "statesync_version.cpp"
  "statesync_version.h")

target_include_directories(monad_statesync PUBLIC ${CATEGORY_MAIN_DIR})

monad_compile_options(monad_statesync)
target_link_libraries(monad_statesync PUBLIC monad_execution_ethereum)

monad_add_test_folder(".")

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  add_executable(fuzz_statesync "${PROJECT_SOURCE_DIR}/test/fuzz_statesync.cpp")
  target_compile_options(fuzz_statesync PRIVATE "-fsanitize=fuzzer")
  target_link_options(fuzz_statesync PRIVATE "-fsanitize=fuzzer")
  monad_compile_options(fuzz_statesync)
  target_link_libraries(fuzz_statesync PUBLIC monad_execution)
endif()
