function(monad_test target)
  add_executable(monad_context_c_${target} ${ARGN})
  monad_compile_options(monad_context_c_${target})
  target_link_libraries(monad_context_c_${target} PRIVATE monad_core monad_context_c GTest::GTest GTest::Main)
  target_link_options(monad_context_c_${target} PRIVATE -rdynamic)
  gtest_discover_tests(
    monad_context_c_${target}
    TEST_PREFIX RunLoop/
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

monad_test(context_switcher_test "context_switcher.cpp")
monad_test(more_realistic_benchmark_test "more_realistic_benchmark.cpp")
monad_test(thread_db_test "thread_db_test.cpp")
target_link_libraries(monad_context_c_thread_db_test PRIVATE monad_context_c-custom-binutils-gdb)
