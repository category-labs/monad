cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

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
  set(prog
      "#include <boost/context/fiber.hpp>\nint main(void){\n::boost::context::fiber foo;\nreturn 0;\n}"
  )
  set(CMAKE_REQUIRED_LIBRARIES "Boost::context")
  check_cxx_source_runs("${prog}" BOOST_FIBER_LINKS_WITHOUT_ADDITIONAL_MACROS)
  if(NOT BOOST_FIBER_LINKS_WITHOUT_ADDITIONAL_MACROS)
    set(CMAKE_REQUIRED_DEFINITIONS "-DBOOST_USE_UCONTEXT=1")
    check_cxx_source_runs("${prog}"
                          BOOST_FIBER_LINKS_WITH_BOOST_USE_UCONTEXT_MACRO)
    if(BOOST_FIBER_LINKS_WITH_BOOST_USE_UCONTEXT_MACRO)
      get_target_property(var Boost::context INTERFACE_COMPILE_DEFINITIONS)
      list(APPEND var "-DBOOST_USE_UCONTEXT=1")
      set_target_properties(Boost::context
                            PROPERTIES INTERFACE_COMPILE_DEFINITIONS "${var}")
    else()
      message(
        FATAL_ERROR
          "FATAL: Boost.Context needs additional help to link, and I need to be taught what"
      )
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

add_library(
  monad_core STATIC
  # config
  "src/monad/config.hpp"
  # core
  "src/monad/core/array.hpp"
  "src/monad/core/assert.c"
  "src/monad/core/assert.h"
  "src/monad/core/backtrace.cpp"
  "src/monad/core/backtrace.hpp"
  "src/monad/core/basic_formatter.hpp"
  "src/monad/core/bit_util.h"
  "src/monad/core/byte_string.hpp"
  "src/monad/core/cmemory.hpp"
  "src/monad/core/cpu_relax.h"
  "src/monad/core/endian.hpp"
  "src/monad/core/hash.hpp"
  "src/monad/core/hex_literal.hpp"
  "src/monad/core/keccak.c"
  "src/monad/core/keccak.h"
  "src/monad/core/keccak_impl.S"
  "src/monad/core/likely.h"
  "src/monad/core/math.hpp"
  "src/monad/core/nibble.h"
  "src/monad/core/offset.hpp"
  "src/monad/core/result.hpp"
  "src/monad/core/size_of.hpp"
  "src/monad/core/small_prng.hpp"
  "src/monad/core/spinlock.h"
  "src/monad/core/tl_tid.c"
  "src/monad/core/tl_tid.h"
  "src/monad/core/unaligned.hpp"
  "src/monad/lru/lru_cache.hpp"
  "src/monad/mem/batch_mem_pool.hpp"
  "src/monad/synchronization/spin_lock.hpp"
  # fiber
  "src/monad/fiber/config.hpp"
  "src/monad/fiber/priority_algorithm.cpp"
  "src/monad/fiber/priority_algorithm.hpp"
  "src/monad/fiber/priority_pool.cpp"
  "src/monad/fiber/priority_pool.hpp"
  "src/monad/fiber/priority_properties.hpp"
  "src/monad/fiber/priority_queue.cpp"
  "src/monad/fiber/priority_queue.hpp"
  "src/monad/fiber/priority_task.hpp"
  # io
  "src/monad/io/buffer_pool.cpp"
  "src/monad/io/buffer_pool.hpp"
  "src/monad/io/buffers.cpp"
  "src/monad/io/buffers.hpp"
  "src/monad/io/config.hpp"
  "src/monad/io/ring.cpp"
  "src/monad/io/ring.hpp"
  # mem
  "src/monad/mem/cpool.h"
  "src/monad/mem/dynamic_allocator.hpp"
  "src/monad/mem/huge_mem.c"
  "src/monad/mem/huge_mem.cpp"
  "src/monad/mem/huge_mem.h"
  "src/monad/mem/huge_mem.hpp"
  "src/monad/mem/mem_map.cpp"
  "src/monad/mem/mem_map.hpp"
  "src/monad/mem/pool_allocator.cpp"
  "src/monad/mem/pool_allocator.hpp"
  # rlp
  "src/monad/rlp/config.hpp"
  "src/monad/rlp/encode.hpp"
  # test
  "src/monad/test/gtest_signal_stacktrace_printer.hpp"
  # util
  "src/monad/util/stopwatch.hpp")
target_include_directories(monad_core PUBLIC "src")
monad_compile_options(monad_core)
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
  "src/monad/core/math_disas.cpp"
  "src/monad/core/offset_disas.cpp"
  "src/monad/core/spinlock_disas.c"
  "src/monad/mem/cpool_disas.c"
  # rlp
  "src/monad/rlp/encode_disas.cpp")
monad_compile_options(monad_core_disas)
target_link_libraries(monad_core_disas PUBLIC monad_core)

# ##############################################################################
# tests
# ##############################################################################

enable_testing()

find_package(GTest REQUIRED)

add_subdirectory("test")

monad_add_test(bit_util_test src/monad/core/bit_util_test.cpp)
monad_add_test(huge_mem_test src/monad/mem/huge_mem_test.cpp)
