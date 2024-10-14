function(monad_test target)
  add_executable(monad_async_c_${target} ${ARGN})
  monad_compile_options(monad_async_c_${target})
  target_link_libraries(monad_async_c_${target} PRIVATE monad_async_c GTest::GTest GTest::Main)
  target_link_options(monad_async_c_${target} PRIVATE -rdynamic)
  gtest_discover_tests(
    monad_async_c_${target}
    TEST_PREFIX RunLoop/
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

monad_test(cancellation_test "cancellation.cpp")

monad_test(executor_test "executor.cpp")

monad_test(file_io_test "file_io.cpp")

monad_test(foreign_executor_test "foreign_executor.cpp")

monad_test(socket_io_test "socket_io.cpp")

monad_test(work_dispatcher_test "work_dispatcher.cpp")
