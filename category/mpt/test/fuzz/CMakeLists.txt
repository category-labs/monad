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

enable_testing()

function(add_trie_fuzztest name)
  foreach(fixture_type in_memory_trie_fixture_t on_disk_fixture_t)
    set(target monad-trie-fuzz-${name}-${fixture_type})
    add_executable(${target} "${name}.cpp")
    if(LIBFUZZER_RUNTIME_PATH AND EXISTS "${LIBFUZZER_RUNTIME_PATH}")
      target_compile_options(${target} PRIVATE "-fsanitize=fuzzer-no-link")
    else()
      message(
        STATUS
          "Using default libFuzzer runtime for target ${target}; set LIBFUZZER_RUNTIME_PATH to use a libc++ build"
      )
      target_compile_options(${target} PRIVATE "-fsanitize=fuzzer")
      target_link_options(${target} PRIVATE "-fsanitize=fuzzer")
    endif()
    target_compile_definitions(
      ${target}
      PRIVATE "MONAD_TRIE_FUZZTEST_FIXTURE=monad::test::${fixture_type}")
    monad_compile_options(${target})
    target_link_libraries(${target} PUBLIC monad_execution)
    if(LIBFUZZER_RUNTIME_PATH AND EXISTS "${LIBFUZZER_RUNTIME_PATH}")
      target_link_libraries(${target} PRIVATE "${LIBFUZZER_RUNTIME_PATH}")
    endif()
    # Set by the clang-fuzz.cmake toolchain file
    if(CMAKE_CXX_FLAGS MATCHES "-DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION")
      # Run sixteen parallel cooperating fuzzers for ten seconds
      add_test(NAME ${target} COMMAND $<TARGET_FILE:${target}>
                                      -max_total_time=10 -fork=16)
      # For some reason this needs to be explicitly specified on my system to
      # yield printing backtraces
      set_tests_properties(
        ${target} PROPERTIES ENVIRONMENT
                             "ASAN_SYMBOLIZER_PATH=/usr/bin/llvm-symbolizer")
    endif()
  endforeach()
endfunction()

add_trie_fuzztest(generated_kv)
add_trie_fuzztest(one_hundred_updates)
