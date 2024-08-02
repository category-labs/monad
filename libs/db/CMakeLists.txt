cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)

project(monad_trie)
enable_testing()

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)
# ##############################################################################
# deps
# ##############################################################################

find_package(
  Boost 1.83 # 1.83 really is the minimum
  COMPONENTS context fiber json thread
  REQUIRED)
find_package(GTest)
find_package(PkgConfig REQUIRED)

pkg_check_modules(archive REQUIRED IMPORTED_TARGET libarchive)
pkg_check_modules(zstd REQUIRED IMPORTED_TARGET libzstd)

# ##############################################################################
# libs
# ##############################################################################

add_library(
  monad_trie STATIC
  "src/monad/mpt/compute.cpp"
  "src/monad/mpt/compute.hpp"
  "src/monad/mpt/config.hpp"
  "src/monad/mpt/copy_trie.cpp"
  "src/monad/mpt/db.cpp"
  "src/monad/mpt/db.hpp"
  "src/monad/mpt/db_error.hpp"
  "src/monad/mpt/find.cpp"
  "src/monad/mpt/find_notify_fiber.cpp"
  "src/monad/mpt/find_request_sender.cpp"
  "src/monad/mpt/find_request_sender.hpp"
  "src/monad/mpt/logger.h"
  "src/monad/mpt/logger.c"
  "src/monad/mpt/nibbles_view.hpp"
  "src/monad/mpt/nibbles_view_fmt.hpp"
  "src/monad/mpt/node.cpp"
  "src/monad/mpt/node.hpp"
  "src/monad/mpt/node_cursor.hpp"
  "src/monad/mpt/ondisk_db_config.hpp"
  "src/monad/mpt/request.hpp"
  "src/monad/mpt/state_machine.hpp"
  "src/monad/mpt/traverse.hpp"
  "src/monad/mpt/trie.cpp"
  "src/monad/mpt/trie.hpp"
  "src/monad/mpt/update.hpp"
  "src/monad/mpt/update_aux.cpp"
  "src/monad/mpt/util.hpp")
target_include_directories(monad_trie PUBLIC "src")
target_include_directories(monad_trie PRIVATE "third_party")
monad_compile_options(monad_trie)
target_link_libraries(monad_trie PRIVATE Boost::boost)
target_link_libraries(monad_trie PUBLIC monad_async)
add_executable(monad_mpt "src/monad/mpt/cli_tool_main.cpp"
                         "src/monad/mpt/cli_tool_impl.cpp")
monad_compile_options(monad_mpt)
target_link_libraries(monad_mpt PUBLIC monad_trie PkgConfig::zstd
                                       PkgConfig::archive CLI11::CLI11)

function(add_trie_test)
  set(ONE_VALUE_ARGS TARGET TEST_FILTER)
  set(MULTI_VALUE_ARGS SOURCES LINK_LIBRARIES)
  cmake_parse_arguments(ADD_TRIE_TEST "" "${ONE_VALUE_ARGS}"
                        "${MULTI_VALUE_ARGS}" ${ARGN})

  add_executable(${ADD_TRIE_TEST_TARGET} ${ADD_TRIE_TEST_SOURCES})
  monad_compile_options(${ADD_TRIE_TEST_TARGET})
  target_link_libraries(
    ${ADD_TRIE_TEST_TARGET} PUBLIC monad_trie GTest::gtest_main
                                   ${ADD_TRIE_TEST_LINK_LIBRARIES})
  gtest_discover_tests(
    ${ADD_TRIE_TEST_TARGET}
    TEST_PREFIX ${PROJECT_NAME}/ TEST_FILTER ${ADD_TRIE_TEST_TEST_FILTER}
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

add_subdirectory("src/monad/mpt/test")

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  add_subdirectory("src/monad/mpt/test/fuzz")
endif()
