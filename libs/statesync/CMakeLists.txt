cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad_statesync)

add_library(
  monad_statesync
  # server
  "src/monad/statesync/statesync_client.cpp"
  "src/monad/statesync/statesync_client.h"
  "src/monad/statesync/statesync_client_context.cpp"
  "src/monad/statesync/statesync_client_context.hpp"
  "src/monad/statesync/statesync_messages.h"
  "src/monad/statesync/statesync_server.cpp"
  "src/monad/statesync/statesync_server.h"
  "src/monad/statesync/statesync_server_context.cpp"
  "src/monad/statesync/statesync_server_context.hpp"
  "src/monad/statesync/statesync_server_context.hpp")

target_include_directories(monad_statesync PUBLIC ${PROJECT_SOURCE_DIR}/src)

monad_compile_options(monad_statesync)
target_link_libraries(monad_statesync PUBLIC monad_execution)

monad_add_test_folder("src/monad/statesync")
