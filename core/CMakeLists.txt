cmake_minimum_required(VERSION 3.25)

cmake_policy(SET CMP0144 NEW) ## find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)
include(CheckCXXSymbolExists)

project(monad_core LANGUAGES C CXX ASM)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# ##############################################################################
# deps
# ##############################################################################

include("cmake/find_our_dependency.cmake")

cmake_host_system_information(RESULT linux_flavour QUERY DISTRIB_ID)
if(linux_flavour MATCHES "debian|ubuntu")
  find_package(Boost REQUIRED COMPONENTS context fiber stacktrace_backtrace)
else()
  find_package(Boost REQUIRED COMPONENTS context fiber stacktrace_addr2line)
endif()
function(check_if_boost_fiber_needs_ucontext_macro)
  set(prog "#include <boost/context/fiber.hpp>\nint main(void){\n::boost::context::fiber foo;\nreturn 0;\n}")
  set(CMAKE_REQUIRED_LIBRARIES "Boost::context")
  check_cxx_source_runs("${prog}" BOOST_FIBER_LINKS_WITHOUT_ADDITIONAL_MACROS)
  if(NOT BOOST_FIBER_LINKS_WITHOUT_ADDITIONAL_MACROS)
    set(CMAKE_REQUIRED_DEFINITIONS "-DBOOST_USE_UCONTEXT=1")
    check_cxx_source_runs("${prog}" BOOST_FIBER_LINKS_WITH_BOOST_USE_UCONTEXT_MACRO)
    if(BOOST_FIBER_LINKS_WITH_BOOST_USE_UCONTEXT_MACRO)
      get_target_property(var Boost::context INTERFACE_COMPILE_DEFINITIONS)
      list(APPEND var "-DBOOST_USE_UCONTEXT=1")
      set_target_properties(Boost::context PROPERTIES INTERFACE_COMPILE_DEFINITIONS "${var}")
    else()
      message(FATAL_ERROR "FATAL: Boost.Context needs additional help to link, and I need to be taught what")
    endif()
  endif()
endfunction()
check_if_boost_fiber_needs_ucontext_macro()

find_package(TBB REQUIRED)

set(ETHASH_TESTING NO)
add_subdirectory("third_party/ethash")

add_subdirectory("third_party/nanobench")

add_subdirectory("third_party/nlohmann_json" SYSTEM)

add_subdirectory("third_party/unordered_dense")

add_subdirectory("third_party/quill" SYSTEM)

add_library(
  openssl_sha3_asm INTERFACE
  "third_party/openssl/crypto/sha/asm/keccak1600-avx2.S"
  "third_party/openssl/crypto/sha/asm/keccak1600-avx512.S")
target_include_directories(openssl_sha3_asm INTERFACE "third_party/openssl")

# ##############################################################################
# libs
# ##############################################################################

function(monad_core_compile_options target)
  set_property(TARGET ${target} PROPERTY C_STANDARD 23)
  set_property(TARGET ${target} PROPERTY C_STANDARD_REQUIRED ON)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD 23)
  set_property(TARGET ${target} PROPERTY CXX_STANDARD_REQUIRED ON)

  target_compile_options(${target} PRIVATE -Wall -Wextra -Wpedantic
                                           -Wconversion -Werror)

  target_compile_options(
    ${target} PRIVATE $<$<CXX_COMPILER_ID:GNU>:-Wno-missing-field-initializers>)
endfunction()

add_library(
  monad_core STATIC
  "c/include/monad/core/assert.h"
  "c/include/monad/core/bit_util.h"
  "c/include/monad/core/cpu_relax.h"
  "c/include/monad/core/likely.h"
  "c/include/monad/core/spinlock.h"
  "c/include/monad/core/tl_tid.h"
  "c/include/monad/mem/huge_mem.h"
  "c/src/monad/core/assert.c"
  "c/src/monad/core/tl_tid.c"
  "c/src/monad/mem/huge_mem.c"
  # config
  "include/monad/config.hpp"
  # core
  "include/monad/core/array.hpp"
  "include/monad/core/backtrace.hpp"
  "include/monad/core/basic_formatter.hpp"
  "include/monad/core/byte_string.hpp"
  "include/monad/core/cmemory.hpp"
  "include/monad/core/endian.hpp"
  "include/monad/core/hash.hpp"
  "include/monad/core/hex_literal.hpp"
  "include/monad/core/keccak.h"
  "include/monad/core/math.hpp"
  "include/monad/core/nibble.h"
  "include/monad/core/offset.hpp"
  "include/monad/core/result.hpp"
  "include/monad/core/size_of.hpp"
  "include/monad/core/small_prng.hpp"
  "include/monad/core/unaligned.hpp"
  "include/monad/lru/lru_cache.hpp"
  "include/monad/mem/batch_mem_pool.hpp"
  "include/monad/synchronization/spin_lock.hpp"
  "c++/monad/core/backtrace.cpp"
  "c++/monad/core/keccak.c"
  "c++/monad/core/keccak_impl.S"
  # fiber
  "include/monad/fiber/config.hpp"
  "include/monad/fiber/priority_algorithm.hpp"
  "include/monad/fiber/priority_pool.hpp"
  "include/monad/fiber/priority_properties.hpp"
  "include/monad/fiber/priority_queue.hpp"
  "include/monad/fiber/priority_task.hpp"
  "c++/monad/fiber/priority_algorithm.cpp"
  "c++/monad/fiber/priority_pool.cpp"
  "c++/monad/fiber/priority_queue.cpp"
  # io
  "include/monad/io/buffer_pool.hpp"
  "include/monad/io/buffers.hpp"
  "include/monad/io/config.hpp"
  "include/monad/io/ring.hpp"
  "c++/monad/io/buffer_pool.cpp"
  "c++/monad/io/buffers.cpp"
  "c++/monad/io/ring.cpp"
  # mem
  "include/monad/mem/cpool.h"
  "include/monad/mem/huge_mem.hpp"
  "include/monad/mem/dynamic_allocator.hpp"
  "include/monad/mem/mem_map.hpp"
  "include/monad/mem/pool_allocator.hpp"
  "c++/monad/mem/huge_mem.cpp"
  "c++/monad/mem/mem_map.cpp"
  "c++/monad/mem/pool_allocator.cpp"
  # rlp
  "include/monad/rlp/config.hpp"
  "include/monad/rlp/encode.hpp"
  # test
  "include/monad/test/gtest_signal_stacktrace_printer.hpp"
  # util
  "include/monad/util/stopwatch.hpp")
target_include_directories(monad_core PUBLIC "include" "c/include")
monad_core_compile_options(monad_core)
target_compile_definitions(monad_core PUBLIC "BOOST_STACKTRACE_LINK=1")
if(linux_flavour MATCHES "debian|ubuntu")
  target_compile_definitions(monad_core
                             PUBLIC "BOOST_STACKTRACE_USE_BACKTRACE=1")
  target_link_libraries(monad_core PUBLIC Boost::stacktrace_backtrace)
else()
  target_compile_definitions(monad_core
                             PUBLIC "BOOST_STACKTRACE_USE_ADDR2LINE=1")
  target_link_libraries(monad_core PUBLIC Boost::stacktrace_addr2line)
endif()
target_link_libraries(monad_core PUBLIC openssl_sha3_asm uring Boost::fiber
                                        TBB::tbb)

add_library(
  monad_core_disas STATIC
  # core
  "c/src/monad/core/spinlock_disas.c"
  # core
  "c++/monad/core/math_disas.cpp"
  "c++/monad/core/offset_disas.cpp"
  "c++/monad/mem/cpool_disas.c"
  # rlp
  "c++/monad/rlp/encode_disas.cpp")
monad_core_compile_options(monad_core_disas)
target_link_libraries(monad_core_disas PUBLIC monad_core)

# ##############################################################################
# tests
# ##############################################################################

enable_testing()

find_package(GTest REQUIRED)

add_subdirectory("test")

monad_add_test(bit_util_test c/src/monad/core/bit_util_test.cpp)
monad_add_test(huge_mem_test c/src/monad/mem/huge_mem_test.cpp)
