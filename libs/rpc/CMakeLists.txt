cmake_minimum_required(VERSION 3.20)

project(monad_rpc)

add_library(
  monad_rpc STATIC
  # rpc
  "src/monad/rpc/eth_call.cpp"
  "src/monad/rpc/eth_call.hpp"
)

target_include_directories(monad_rpc PUBLIC ${PROJECT_SOURCE_DIR}/src)

monad_compile_options(monad_rpc)

target_link_libraries(monad_rpc PRIVATE monad_execution)
