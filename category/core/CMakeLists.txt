# Copyright (C) 2025 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

include(CheckCXXSourceRuns)
include(CheckCXXSymbolExists)

project(monad_core LANGUAGES C CXX ASM)

option(CMAKE_EXPORT_COMPILE_COMMANDS ON)

option(MONAD_CORE_FORCE_DEBUG_ASSERT
       "Enable MONAD_DEBUG_ASSERT in any build mode" OFF)

# ##############################################################################
# deps
# ##############################################################################

include("cmake/find_our_dependency.cmake")

find_package(
  Boost CONFIG REQUIRED
  COMPONENTS context fiber stacktrace_basic
  OPTIONAL_COMPONENTS stacktrace_backtrace)

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

# ##############################################################################
# libs
# ##############################################################################

add_library(
  monad_core OBJECT
  # config
  "config.hpp"
  # core
  "assert.c"
  "assert.h"
  "backtrace.cpp"
  "backtrace.hpp"
  "basic_formatter.hpp"
  "blake3.hpp"
  "byte_string.hpp"
  "bytes.hpp"
  "bytes_hash_compare.hpp"
  "cleanup.h"
  "cleanup.c"
  "cpu_relax.h"
  "endian.hpp"
  "format_err.c"
  "format_err.h"
  "hash.hpp"
  "int.hpp"
  "is_specialization_of.hpp"
  "keccak.c"
  "keccak.h"
  "keccak.hpp"
  "likely.h"
  "log_ffi.cpp"
  "log_ffi.h"
  "math.hpp"
  "monad_exception.cpp"
  "monad_exception.hpp"
  "nibble.h"
  "path_util.c"
  "path_util.h"
  "result.hpp"
  "size_of.hpp"
  "small_prng.hpp"
  "spinlock.h"
  "srcloc.h"
  "tl_tid.c"
  "tl_tid.h"
  "unaligned.hpp"
  "lru/lru_cache.hpp"
  "lru/static_lru_cache.hpp"
  "mem/batch_mem_pool.hpp"
  "synchronization/spin_lock.hpp"
  # event
  "event/event_iterator.h"
  "event/event_iterator_inline.h"
  "event/event_metadata.h"
  "event/event_recorder.h"
  "event/event_recorder_inline.h"
  "event/event_ring.c"
  "event/event_ring.h"
  "event/event_ring_util.c"
  "event/event_ring_util.h"
  "event/test_event_ctypes.h"
  "event/test_event_ctypes_metadata.c"
  # fiber
  "fiber/config.hpp"
  "fiber/fiber_group.cpp"
  "fiber/fiber_group.hpp"
  "fiber/fiber_thread_pool.cpp"
  "fiber/fiber_thread_pool.hpp"
  "fiber/priority_algorithm.cpp"
  "fiber/priority_algorithm.hpp"
  "fiber/priority_pool.cpp"
  "fiber/priority_pool.hpp"
  "fiber/priority_properties.hpp"
  "fiber/priority_queue.cpp"
  "fiber/priority_queue.hpp"
  "fiber/priority_task.hpp"
  # io
  "io/buffer_pool.cpp"
  "io/buffer_pool.hpp"
  "io/config.hpp"
  # mem
  "mem/align.h"
  # rlp
  "rlp/config.hpp"
  "rlp/encode.hpp"
  # runtime
  "runtime/non_temporal_memory.hpp"
  "runtime/uint256.cpp"
  "runtime/uint256.hpp"
  # test
  "test_util/gtest_signal_stacktrace_printer.hpp"
  # util
  "util/stopwatch.hpp")

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  # Append Linux-specific implementation files
  target_sources(
    monad_core
    PRIVATE # core
            "cpuset.c"
            "cpuset.h"
            # event
            "event/event_ring_util_linux.c"
            # io
            "io/buffers.cpp"
            "io/buffers.hpp"
            "io/ring.hpp"
            "io/ring.cpp"
            # mem
            "mem/huge_mem.hpp"
            "mem/huge_mem.cpp"
            "mem/hugetlb_path.c"
            "mem/hugetlb_path.h"
            # procfs
            "procfs/statm.c"
            "procfs/statm.h")
endif()

target_include_directories(monad_core PRIVATE "${THIRD_PARTY_DIR}/openssl")
if(${CMAKE_SYSTEM_PROCESSOR} MATCHES "x86_64")
  target_sources(monad_core PRIVATE "keccak_impl.S")
else()
  target_sources(monad_core
                 PRIVATE "third_party/openssl/crypto/sha/keccak1600.c")
endif()

monad_compile_options(monad_core)
target_include_directories(monad_core PUBLIC ${CATEGORY_MAIN_DIR})

if(MONAD_CORE_FORCE_DEBUG_ASSERT)
  target_compile_definitions(monad_core PUBLIC "MONAD_CORE_FORCE_DEBUG_ASSERT")
endif()

target_compile_definitions(monad_core PRIVATE "BOOST_STACKTRACE_LINK=1")
if(TARGET Boost::stacktrace_backtrace)
  target_compile_definitions(monad_core
                             PRIVATE BOOST_STACKTRACE_USE_BACKTRACE=1)
  target_link_libraries(monad_core PRIVATE Boost::stacktrace_backtrace)
else()
  message(WARNING "using suboptimal basic backtrace library")
  target_link_libraries(monad_core PRIVATE Boost::stacktrace_basic)
endif()

target_link_libraries(monad_core PUBLIC ankerl_hash)
target_link_libraries(monad_core PUBLIC Boost::fiber TBB::tbb)
target_link_libraries(monad_core PUBLIC komihash)
target_link_libraries(monad_core PUBLIC blake3)
target_link_libraries(monad_core PUBLIC ethash::keccak)
target_link_libraries(monad_core PUBLIC evmc)
target_link_libraries(monad_core PUBLIC intx)
target_link_libraries(monad_core PUBLIC quill)
target_link_libraries(monad_core PUBLIC unordered_dense)
target_link_libraries(monad_core PUBLIC PkgConfig::zstd)
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  target_link_libraries(monad_core PUBLIC hugetlbfs uring)
endif()

add_library(
  monad_core_disas STATIC
  # core
  "math_disas.cpp" "spinlock_disas.c"
  # rlp
  "rlp/encode_disas.cpp")
monad_compile_options(monad_core_disas)
target_link_libraries(monad_core_disas PUBLIC monad_core)

# ##############################################################################
# tests
# ##############################################################################

enable_testing()

find_package(GTest REQUIRED)

add_subdirectory("test")

monad_add_test(static_lru_test lru/static_lru_test.cpp)
