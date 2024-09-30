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
  Boost REQUIRED
  COMPONENTS context fiber stacktrace_basic
  OPTIONAL_COMPONENTS stacktrace_addr2line stacktrace_backtrace)

if(TARGET Boost::stacktrace_backtrace)
  set(BOOST_STACKTRACE_TARGET Boost::stacktrace_backtrace)
  set(BOOST_STACKTRACE_OPTIONS BOOST_STACKTRACE_USE_BACKTRACE=1)
elseif(TARGET Boost::stacktrace_addr2line)
  set(BOOST_STACKTRACE_TARGET Boost::stacktrace_addr2line)
  set(BOOST_STACKTRACE_OPTIONS BOOST_STACKTRACE_USE_ADDR2LINE=1)
  message(
    WARNING "using suboptimal backtrace library ${BOOST_STACKTRACE_TARGET}")
else()
  set(BOOST_STACKTRACE_TARGET Boost::stacktrace_basic)
  message(
    WARNING "using suboptimal backtrace library ${BOOST_STACKTRACE_TARGET}")
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

# monad_core_c is a library containing source code that is compiled in C23 mode
# and contains no C++ source files; it may be linked by downstream libraries
# which only need C and do not want the C++ runtime as a dependency
add_library(
  monad_core_c OBJECT
  "src/monad/core/assert.c"
  "src/monad/core/assert.h")
monad_compile_options(monad_core_c)
if(MONAD_CORE_FORCE_DEBUG_ASSERT)
  target_compile_definitions(monad_core_c
                             PUBLIC "MONAD_CORE_FORCE_DEBUG_ASSERT")
endif()
target_include_directories(monad_core_c PUBLIC "src")

add_library(
  monad_core STATIC
  # config
  "src/monad/config.hpp"
  # core
  "src/monad/core/array.hpp"
  "src/monad/core/backtrace.cpp"
  "src/monad/core/backtrace.hpp"
  "src/monad/core/basic_formatter.hpp"
  "src/monad/core/bit_util.h"
  "src/monad/core/byte_string.hpp"
  "src/monad/core/bytes_hash_compare.hpp"
  "src/monad/core/cmemory.hpp"
  "src/monad/core/cleanup.h"
  "src/monad/core/cleanup.c"
  "src/monad/core/cpu_relax.h"
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
  "src/monad/core/spinlock.h"
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
  "src/monad/io/config.hpp"
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
    monad_core PRIVATE
    # core
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

# The configuration that needs to be added for the Boost stacktrace library is
# modeled as an interface target, so it can be linked to both `monad_core` and
# `monad_core_crt`
add_library(monad_core_stacktrace_options INTERFACE)
target_compile_definitions(monad_core_stacktrace_options
                           INTERFACE "BOOST_STACKTRACE_LINK=1")
target_compile_definitions(monad_core_stacktrace_options
                           INTERFACE ${BOOST_STACKTRACE_OPTIONS})
target_link_libraries(monad_core_stacktrace_options
                      INTERFACE ${BOOST_STACKTRACE_TARGET})

target_link_libraries(monad_core PUBLIC monad_core_c)
target_link_libraries(monad_core PRIVATE monad_core_stacktrace_options)

target_link_libraries(monad_core PUBLIC openssl_sha3 Boost::fiber TBB::tbb)
target_link_libraries(monad_core PUBLIC komihash)
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

# Minimal "runtime" library needed to support pure C binaries. This contains
# functions that have C linkage and follow the C ABI but are implemented in C++.
# This is a dynamic library that statically links to the C++ runtime libraries
# and hides all symbols except those the `monad_` prefix, so it cannot relocate
# against any other dynamically loaded C++ runtime. All source files are
# recompiled rather than some other kind of reuse mechanism because the code
# generation must enable position independent code.
add_library(
  monad_core_crt SHARED
  # config
  "src/monad/config.hpp"
  # core
  "src/monad/core/backtrace.cpp"
  "src/monad/core/backtrace.hpp")
set_target_properties(monad_core_crt PROPERTIES
        CXX_VISIBILITY_PRESET hidden
        VISIBILITY_INLINES_HIDDEN ON)
target_include_directories(monad_core_crt PUBLIC "src")
monad_compile_options(monad_core_crt)
target_link_libraries(monad_core_crt PRIVATE monad_core_stacktrace_options)
if(NOT APPLE)
  if("${CMAKE_CXX_FLAGS}" MATCHES ".*-fsanitize=.*" AND
     CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    target_compile_options(monad_core_crt PUBLIC "-fno-sanitize=function,vptr")
  endif()
  target_link_options(monad_core_crt PRIVATE -static-libstdc++)
  target_link_options(
    monad_core_crt
    PRIVATE
    "-Wl,--version-script=${CMAKE_CURRENT_SOURCE_DIR}/src/monad/core/core_crt.sym"
  )
endif()

# ##############################################################################
# tests
# ##############################################################################

enable_testing()

find_package(GTest REQUIRED)

add_subdirectory("test")

monad_add_test(bit_util_test src/monad/core/bit_util_test.cpp)
monad_add_test(static_lru_test src/monad/lru/static_lru_test.cpp)
