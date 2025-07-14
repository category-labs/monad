enable_testing()

function(add_trie_fuzztest name)
  foreach(fixture_type in_memory_trie_fixture_t on_disk_fixture_t)
    set(target monad-trie-fuzz-${name}-${fixture_type})
    add_executable(${target} "${name}.cpp")
    target_compile_options(${target} PRIVATE "-fsanitize=fuzzer")
    target_compile_definitions(
      ${target}
      PRIVATE "MONAD_TRIE_FUZZTEST_FIXTURE=monad::test::${fixture_type}")
    target_link_options(${target} PRIVATE "-fsanitize=fuzzer")
    monad_compile_options(${target})
    target_link_libraries(${target} PUBLIC monad_trie)
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
