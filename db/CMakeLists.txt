cmake_minimum_required(VERSION 3.21)

cmake_policy(SET CMP0144 NEW) ## find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)

project(monad_trie)
enable_testing()

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)
# ##############################################################################
# deps
# ##############################################################################

find_package(
  Boost 1.83  ## 1.83 really is the minimum
  COMPONENTS context fiber json thread
  REQUIRED)
find_package(CLI11 REQUIRED)
find_package(GTest)
find_package(PkgConfig REQUIRED)

pkg_check_modules(archive REQUIRED IMPORTED_TARGET libarchive)
pkg_check_modules(cap REQUIRED IMPORTED_TARGET libcap)
pkg_check_modules(zstd REQUIRED IMPORTED_TARGET libzstd)

  
# ##############################################################################
# libs
# ##############################################################################
add_library(
  monad_async STATIC
  "${PROJECT_SOURCE_DIR}/src/monad/async/boost_fiber_wrappers.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/async/io.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/async/storage_pool.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/async/util.cpp")
target_include_directories(monad_async PUBLIC "${PROJECT_SOURCE_DIR}/include")
monad_core_compile_options(monad_async)
target_link_libraries(monad_async PUBLIC monad_core Boost::fiber)

add_library(
  monad_trie STATIC
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/config.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/compute.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/db.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/db_error.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/find_request_sender.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/mem.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/nibbles_view.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/nibbles_view_fmt.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/node.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/node_cursor.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/ondisk_db_config.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/request.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/state_machine.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/traverse.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/trie.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/util.hpp"
  "${PROJECT_SOURCE_DIR}/include/monad/mpt/update.hpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/compute.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/copy_node.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/db.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/find_notify_fiber.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/find_request_sender.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/find.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/mem.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/node.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/traverse.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/trie.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/update_aux.cpp")
target_include_directories(
  monad_trie PUBLIC
  "${PROJECT_SOURCE_DIR}/include"
)
target_include_directories(
  monad_trie PRIVATE
  "${PROJECT_SOURCE_DIR}/third_party"
)
monad_core_compile_options(monad_trie)
target_link_libraries(monad_trie PRIVATE Boost::boost)
target_link_libraries(monad_trie PUBLIC monad_async)
target_link_libraries(monad_trie PUBLIC monad_core)
add_executable(monad_mpt "${PROJECT_SOURCE_DIR}/src/monad/mpt/cli_tool_main.cpp"
  "${PROJECT_SOURCE_DIR}/src/monad/mpt/cli_tool_impl.cpp")
monad_core_compile_options(monad_mpt)
target_link_libraries(monad_mpt PUBLIC monad_trie PkgConfig::zstd PkgConfig::archive CLI11::CLI11)

function(add_trie_test)
  set(ONE_VALUE_ARGS TARGET TEST_FILTER)
  set(MULTI_VALUE_ARGS SOURCES LINK_LIBRARIES)
  cmake_parse_arguments(ADD_TRIE_TEST "" "${ONE_VALUE_ARGS}"
                        "${MULTI_VALUE_ARGS}" ${ARGN})

  add_executable(${ADD_TRIE_TEST_TARGET} ${ADD_TRIE_TEST_SOURCES})
  monad_core_compile_options(${ADD_TRIE_TEST_TARGET})
  target_link_libraries(${ADD_TRIE_TEST_TARGET} PUBLIC monad_trie
                                                       GTest::gtest_main
                                                       ${ADD_TRIE_TEST_LINK_LIBRARIES}
  )
  gtest_discover_tests(
    ${ADD_TRIE_TEST_TARGET}
    TEST_PREFIX ${PROJECT_NAME}/ TEST_FILTER ${ADD_TRIE_TEST_TEST_FILTER}
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1
    ENVIRONMENT UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1
    ENVIRONMENT TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

add_subdirectory("src/monad/mpt/test")
add_subdirectory("src/monad/async/test")

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
  add_subdirectory("src/monad/mpt/test/fuzz")
endif()
