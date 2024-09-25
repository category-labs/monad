cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)
include(CheckCXXSymbolExists)

project(monad_core LANGUAGES C CXX ASM)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  set(_monad_spinlock_track_owner_info ON)
  set(_monad_spinlock_track_stats ON)
else()
  set(_monad_spinlock_track_owner_info OFF)
  set(_monad_spinlock_track_stats OFF)
endif()

option(MONAD_CORE_FORCE_DEBUG_ASSERT
       "Enable MONAD_DEBUG_ASSERT in any build mode" OFF)

option(MONAD_CORE_SPINLOCK_TRACK_OWNER_INFO
       "enable source location of owner in spinlocks"
       ${_monad_spinlock_track_owner_info})
option(MONAD_CORE_SPINLOCK_TRACK_STATS
       "enable contention statistics tracking of spinlocks"
       ${_monad_spinlock_track_stats})
option(MONAD_CORE_SPINLOCK_TRACK_STATS_ATOMIC
       "use fetch_add on atomics statistics tracking" OFF)

# This is reasonable behavior to have, that is not strictly needed at the moment
# for `monad` but could cause surprises later and failures in the test suite.
# This should be the normal behavior (without a configuration option) if we can
# figure out how to avoid the slight performance hit
option(MONAD_CORE_RUN_QUEUE_SUPPORT_EQUAL_PRIO
       "Allow the run_queue to support equal priority fibers" ON)

# ##############################################################################
# deps
# ##############################################################################

include("cmake/find_our_dependency.cmake")

find_package(Boost REQUIRED
  COMPONENTS stacktrace_basic
  OPTIONAL_COMPONENTS stacktrace_backtrace)

find_package(TBB REQUIRED)

add_subdirectory("third_party/nanobench")

add_subdirectory("third_party/nlohmann_json" SYSTEM)

add_subdirectory("third_party/unordered_dense")

add_subdirectory("third_party/quill" SYSTEM)

add_library(openssl_sha3 OBJECT)
target_include_directories(openssl_sha3 PRIVATE "third_party/openssl")
if(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86_64")
  target_sources(openssl_sha3 PRIVATE "src/monad/core/keccak_impl.S")
else()
  target_sources(openssl_sha3
                 PRIVATE "third_party/openssl/crypto/sha/keccak1600.c")
endif()

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
  "src/monad/core/blake3.hpp"
  "src/monad/core/boost_result.h"
  "src/monad/core/byte_string.hpp"
  "src/monad/core/bytes_hash_compare.hpp"
  "src/monad/core/cmemory.hpp"
  "src/monad/core/cleanup.h"
  "src/monad/core/cleanup.c"
  "src/monad/core/c_result.cpp"
  "src/monad/core/c_result.h"
  "src/monad/core/endian.hpp"
  "src/monad/core/hash.hpp"
  "src/monad/core/hex_literal.hpp"
  "src/monad/core/keccak.c"
  "src/monad/core/keccak.h"
  "src/monad/core/keccak.hpp"
  "src/monad/core/likely.h"
  "src/monad/core/math.hpp"
  "src/monad/core/nibble.h"
  "src/monad/core/offset.hpp"
  "src/monad/core/result.hpp"
  "src/monad/core/size_of.hpp"
  "src/monad/core/small_prng.hpp"
  "src/monad/core/srcloc.hpp"
  "src/monad/core/tl_tid.c"
  "src/monad/core/tl_tid.h"
  "src/monad/core/unaligned.hpp"
  "src/monad/core/unordered_map.hpp"
  "src/monad/lru/lru_cache.hpp"
  "src/monad/lru/static_lru_cache.hpp"
  "src/monad/mem/batch_mem_pool.hpp"
  "src/monad/synchronization/spin_lock.hpp"
  # fiber
  "src/monad/fiber/config.hpp"
  "src/monad/fiber/fiber.c"
  "src/monad/fiber/fiber.h"
  "src/monad/fiber/fiber_channel.h"
  "src/monad/fiber/fiber_semaphore.h"
  "src/monad/fiber/fiber_inline.h"
  "src/monad/fiber/fiber_thr.c"
  "src/monad/fiber/priority_pool.cpp"
  "src/monad/fiber/priority_pool.hpp"
  "src/monad/fiber/priority_task.hpp"
  "src/monad/fiber/run_queue.c"
  "src/monad/fiber/run_queue.h"
  # io
  "src/monad/io/buffer_pool.cpp"
  "src/monad/io/buffer_pool.hpp"
  "src/monad/io/config.hpp"
  # mem
  "src/monad/mem/align.h"
  "src/monad/mem/cma/cma_alloc.h"
  "src/monad/mem/cma/cma_alloc.c"
  "src/monad/mem/cma/cma_bump_alloc.h"
  "src/monad/mem/cma/cma_bump_alloc.c"
  "src/monad/mem/cma/cma_fallback.h"
  "src/monad/mem/cma/cma_fallback.c"
  # rlp
  "src/monad/rlp/config.hpp"
  "src/monad/rlp/encode.hpp"
  # test
  "src/monad/test/gtest_signal_stacktrace_printer.hpp"
  # util
  "src/monad/util/stopwatch.hpp")

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  # Append Linux-specific implementation files
  target_sources(
    monad_core
    PRIVATE # core
            "src/monad/core/cgroup.c"
            "src/monad/core/cgroup.h"
            "src/monad/core/cpuset.c"
            "src/monad/core/cpuset.h"
            # io
            "src/monad/io/buffers.cpp"
            "src/monad/io/buffers.hpp"
            "src/monad/io/ring.hpp"
            "src/monad/io/ring.cpp"
            # mem
            "src/monad/mem/huge_mem.hpp"
            "src/monad/mem/huge_mem.cpp"
            # procfs
            "src/monad/procfs/statm.c"
            "src/monad/procfs/statm.h")
endif()

monad_compile_options(monad_core)
target_include_directories(monad_core PUBLIC "src")

if(MONAD_CORE_FORCE_DEBUG_ASSERT)
  target_compile_definitions(monad_core PUBLIC "MONAD_CORE_FORCE_DEBUG_ASSERT")
endif()

if(MONAD_CORE_SPINLOCK_TRACK_OWNER_INFO)
  target_compile_definitions(monad_core PUBLIC MONAD_SPINLOCK_TRACK_OWNER_INFO)
endif()

if(MONAD_CORE_SPINLOCK_TRACK_STATS)
  target_compile_definitions(monad_core PUBLIC MONAD_SPINLOCK_TRACK_STATS)
endif()

if(MONAD_CORE_SPINLOCK_TRACK_STATS_ATOMIC)
  target_compile_definitions(monad_core
                             PUBLIC MONAD_SPINLOCK_TRACK_STATS_ATOMIC)
endif()

if(MONAD_CORE_RUN_QUEUE_SUPPORT_EQUAL_PRIO)
  target_compile_definitions(monad_core
                             PUBLIC MONAD_CORE_RUN_QUEUE_SUPPORT_EQUAL_PRIO)
endif()

target_link_libraries(monad_core PUBLIC monad_boost_context)

target_compile_definitions(monad_core PRIVATE "BOOST_STACKTRACE_LINK=1")
if(TARGET Boost::stacktrace_backtrace)
  target_compile_definitions(monad_core
                             PRIVATE BOOST_STACKTRACE_USE_BACKTRACE=1)
  target_link_libraries(monad_core PRIVATE Boost::stacktrace_backtrace)
else()
  message(WARNING "using suboptimal basic backtrace library")
  target_link_libraries(monad_core PRIVATE Boost::stacktrace_basic)
endif()

target_link_libraries(monad_core PUBLIC openssl_sha3 TBB::tbb)
target_link_libraries(monad_core PUBLIC komihash)
target_link_libraries(monad_core PUBLIC blake3)
target_link_libraries(monad_core PUBLIC ethash::keccak)
target_link_libraries(monad_core PUBLIC evmc)
target_link_libraries(monad_core PUBLIC unordered_dense)

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  target_link_libraries(monad_core PUBLIC cgroup uring)
endif()

add_library(
  monad_core_disas STATIC
  # core
  "src/monad/core/math_disas.cpp"
  "src/monad/core/offset_disas.cpp"
  "src/monad/core/spinlock_disas.c"
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
monad_add_test(static_lru_test src/monad/lru/static_lru_test.cpp)
