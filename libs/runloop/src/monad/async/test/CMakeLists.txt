function(monad_test target)
  cmake_parse_arguments(ADD_TEST "" "" "SOURCES;LINK_LIBRARIES;TEST_PROPERTIES" ${ARGN})
  add_executable(monad_async_c_${target} ${ADD_TEST_SOURCES})
  monad_compile_options(monad_async_c_${target})
  target_link_libraries(monad_async_c_${target} PRIVATE monad_async_c GTest::GTest GTest::Main ${ADD_TEST_LINK_LIBRARIES})
  target_link_options(monad_async_c_${target} PRIVATE -rdynamic)
  gtest_discover_tests(
    monad_async_c_${target}
    TEST_PREFIX RunLoop/
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer
               ${ADD_TEST_TEST_PROPERTIES})
endfunction()

monad_test(cancellation_test SOURCES "cancellation.cpp")

monad_test(executor_test SOURCES "executor.cpp")

monad_test(file_io_test SOURCES "file_io.cpp" TEST_PROPERTIES RUN_SERIAL TRUE)

monad_test(foreign_executor_test SOURCES "foreign_executor.cpp")

monad_test(socket_io_test SOURCES "socket_io.cpp")

monad_test(sorted_ring_buffer_test SOURCES "sorted_ring_buffer_test.cpp")

monad_test(work_dispatcher_test SOURCES "work_dispatcher.cpp")
