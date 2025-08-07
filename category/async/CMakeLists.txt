cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)

project(monad_async)

# ##############################################################################
# deps
# ##############################################################################

find_package(Boost 1.83 # 1.83 really is the minimum
             CONFIG REQUIRED COMPONENTS fiber)

# ##############################################################################
# libs
# ##############################################################################

add_library(
  monad_async
  "concepts.hpp"
  "config.hpp"
  "connected_operation.hpp"
  "detail/connected_operation_storage.hpp"
  "detail/scope_polyfill.hpp"
  "detail/start_lifetime_as_polyfill.hpp"
  "erased_connected_operation.hpp"
  "io.cpp"
  "io.hpp"
  "io_senders.hpp"
  "sender_errc.hpp"
  "storage_pool.cpp"
  "storage_pool.hpp"
  "util.cpp"
  "util.hpp")

target_include_directories(monad_async PUBLIC ${CATEGORY_MAIN_DIR})
monad_compile_options(monad_async)
target_link_libraries(monad_async PUBLIC monad_core Boost::fiber)

# ##############################################################################
# unit tests
# ##############################################################################

function(add_async_test)
  set(ONE_VALUE_ARGS TARGET TEST_FILTER)
  set(MULTI_VALUE_ARGS SOURCES LINK_LIBRARIES)
  cmake_parse_arguments(ADD_TRIE_TEST "" "${ONE_VALUE_ARGS}"
                        "${MULTI_VALUE_ARGS}" ${ARGN})

  add_executable(${ADD_TRIE_TEST_TARGET} ${ADD_TRIE_TEST_SOURCES})
  monad_compile_options(${ADD_TRIE_TEST_TARGET})
  target_link_libraries(
    ${ADD_TRIE_TEST_TARGET} PUBLIC monad_async GTest::gtest_main
                                   ${ADD_TRIE_TEST_LINK_LIBRARIES})
  gtest_discover_tests(
    ${ADD_TRIE_TEST_TARGET}
    TEST_PREFIX ${PROJECT_NAME}/ TEST_FILTER ${ADD_TRIE_TEST_TEST_FILTER}
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

add_subdirectory("test")

# monad async perf test
add_executable(benchmark_io_test "test/benchmark_io_test.cpp")
monad_compile_options(benchmark_io_test)
target_link_libraries(benchmark_io_test PUBLIC monad_core CLI11::CLI11
                                               monad_async)
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  pkg_check_modules(cap IMPORTED_TARGET libcap)
  target_compile_definitions(benchmark_io_test PRIVATE MONAD_HAVE_LIBCAP=1)
  target_link_libraries(benchmark_io_test PRIVATE PkgConfig::cap)
endif()
