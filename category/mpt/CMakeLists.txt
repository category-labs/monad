cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)

project(monad_trie)
enable_testing()

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)
# ##############################################################################
# deps
# ##############################################################################

find_package(Boost 1.83 # 1.83 really is the minimum
             CONFIG REQUIRED COMPONENTS context fiber json thread)
find_package(GTest)
find_package(PkgConfig REQUIRED)

pkg_check_modules(archive REQUIRED IMPORTED_TARGET libarchive)
pkg_check_modules(zstd REQUIRED IMPORTED_TARGET libzstd)

# ##############################################################################
# libs
# ##############################################################################

add_library(
  monad_trie
  OBJECT
  "compute.cpp"
  "compute.hpp"
  "config.hpp"
  "copy_trie.cpp"
  "db.cpp"
  "db.hpp"
  "db_error.hpp"
  "find.cpp"
  "find_notify_fiber.cpp"
  "find_request_sender.hpp"
  "nibbles_view.hpp"
  "nibbles_view_fmt.hpp"
  "node.cpp"
  "node.hpp"
  "node_cursor.hpp"
  "ondisk_db_config.hpp"
  "request.hpp"
  "read_node_blocking.cpp"
  "state_machine.hpp"
  "traverse.hpp"
  "traverse_util.hpp"
  "trie.cpp"
  "trie.hpp"
  "update.hpp"
  "update_aux.cpp"
  "util.hpp")
target_include_directories(monad_trie PUBLIC ${CATEGORY_MAIN_DIR})
target_include_directories(monad_trie PRIVATE "third_party")
monad_compile_options(monad_trie)
target_link_libraries(monad_trie PRIVATE Boost::boost)
target_link_libraries(monad_trie PUBLIC concurrentqueue)
target_link_libraries(monad_trie PUBLIC monad_async)
target_link_libraries(monad_trie PUBLIC quill::quill) # TODO: remove
add_executable(monad_mpt "cli_tool_main.cpp" "cli_tool_impl.cpp")
monad_compile_options(monad_mpt)
target_link_libraries(monad_mpt PUBLIC monad_execution PkgConfig::zstd
                                       PkgConfig::archive CLI11::CLI11)

function(add_trie_test)
  set(ONE_VALUE_ARGS TARGET TEST_FILTER)
  set(MULTI_VALUE_ARGS SOURCES LINK_LIBRARIES)
  cmake_parse_arguments(ADD_TRIE_TEST "" "${ONE_VALUE_ARGS}"
                        "${MULTI_VALUE_ARGS}" ${ARGN})

  add_executable(
    ${ADD_TRIE_TEST_TARGET}
    "${PROJECT_SOURCE_DIR}/../../test/unit/common/src/test/main.cpp"
    ${ADD_TRIE_TEST_SOURCES})
  monad_compile_options(${ADD_TRIE_TEST_TARGET})
  target_link_libraries(
    ${ADD_TRIE_TEST_TARGET}
    PUBLIC monad_execution GTest::GTest monad_unit_test_common
           ${ADD_TRIE_TEST_LINK_LIBRARIES})
  gtest_discover_tests(
    ${ADD_TRIE_TEST_TARGET}
    TEST_PREFIX ${PROJECT_NAME}/ TEST_FILTER ${ADD_TRIE_TEST_TEST_FILTER}
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

add_subdirectory("test")

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  add_subdirectory("test/fuzz")
endif()
