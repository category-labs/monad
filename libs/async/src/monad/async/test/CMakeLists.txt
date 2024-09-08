add_async_test(TARGET cpp_coroutine_wrappers_test SOURCES
              "cpp_coroutine_wrappers.cpp")

add_async_test(TARGET io_test SOURCES "io.cpp")

monad_add_test_death(io_death_write_buffer_exhaustion_causes_death_test
                     SOURCES "io_death_write_buffer_exhaustion_causes_death.cpp"
                     LINK_LIBRARIES monad_async
                     FAIL_REGEX ".*Must fail after this:\nFATAL: no i/o buffers remaining.*")
monad_add_test_death(io_death_read_buffer_exhaustion_causes_death_test
                     SOURCES "io_death_read_buffer_exhaustion_causes_death.cpp"
                     LINK_LIBRARIES monad_async
                     FAIL_REGEX ".*Must fail after this:\nFATAL: no i/o buffers remaining.*")

add_async_test(TARGET io_worker_pool_test SOURCES "io_worker_pool.cpp")
target_link_options(io_worker_pool_test PUBLIC "-rdynamic")
execute_process(
  COMMAND bash -c
          "awk -F= '/^ID=/{print $2}' /etc/os-release | tr -d '\n' | tr -d '\"'"
  OUTPUT_VARIABLE linux_flavour)
if(linux_flavour MATCHES "debian|ubuntu" AND NOT CMAKE_CXX_COMPILER_ID STREQUAL
                                             "Clang")
  # This produces the best backtraces on Debian/Ubuntu, addr2line doesn't work
  # well on those backtrace.h is within GCC's internal headers, so clang doesn't
  # find it.
  target_compile_definitions(io_worker_pool_test
                             PUBLIC "BOOST_STACKTRACE_USE_BACKTRACE=1")
  target_link_libraries(io_worker_pool_test PUBLIC "backtrace")
else()
  # This produces lovely backtraces on CentOS
  target_compile_definitions(io_worker_pool_test
                             PUBLIC "BOOST_STACKTRACE_USE_ADDR2LINE=1")
  target_link_libraries(io_worker_pool_test PUBLIC "dl")
endif()

add_async_test(TARGET storage_pool_test SOURCES "storage_pool.cpp")
