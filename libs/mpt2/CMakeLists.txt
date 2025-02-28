cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad_mpt2)

add_library(
  monad_mpt2 STATIC
  "src/monad/mpt2/config.hpp"
  "src/monad/mpt2/node.hpp"
  "src/monad/mpt2/proof.cpp"
  "src/monad/mpt2/proof.hpp"
  # rlp
  "src/monad/mpt2/rlp/item.hpp"
  "src/monad/mpt2/rlp/item.cpp"
)

target_include_directories(monad_mpt2 PUBLIC ${PROJECT_SOURCE_DIR}/src)

monad_compile_options(monad_mpt2)

target_link_libraries(monad_mpt2 PUBLIC monad_execution)
monad_add_test_folder("src/monad/mpt2")
