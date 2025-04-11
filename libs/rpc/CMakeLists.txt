cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad_rpc)

add_library(
  monad_rpc
  # rpc
  "src/monad/rpc/eth_call.cpp"
  "src/monad/rpc/eth_call.h")

target_include_directories(monad_rpc PUBLIC ${PROJECT_SOURCE_DIR}/src)

monad_compile_options(monad_rpc)
target_link_libraries(monad_rpc PRIVATE monad_execution)

monad_add_test_folder("src/monad/rpc")
