function(monad_add_test target)
  add_executable(${target} ${ARGN})
  monad_compile_options(${target})
  target_link_libraries(${target} monad_core GTest::GTest GTest::Main)
  add_test(NAME ${target} COMMAND $<TARGET_FILE:${target}>)
endfunction()

monad_add_test(allocators_test "allocators.cpp")
monad_add_test(array_test "array.cpp")
monad_add_test(async_signal_handling_test "async_signal_handling_test.cpp")
monad_add_test(backtrace_test "backtrace.cpp")
monad_add_test(cpuset_test "cpuset.cpp")
monad_add_test(encode_test "encode_test.cpp")
monad_add_test(hugemem_test "huge_mem.cpp")
target_link_libraries(hugemem_test GTest::gmock)
monad_add_test(io_buffers_test "io_buffers.cpp")
monad_add_test(literal_test "literal_test.cpp")
monad_add_test(priority_pool_test "priority_pool_test.cpp")
set_tests_properties(priority_pool_test PROPERTIES RUN_SERIAL TRUE)
monad_add_test(unordered_map_test "unordered_map.cpp")

# Need to match failure
add_executable(async_signal_handling_watchdog_test "async_signal_handling_watchdog_test.cpp")
monad_compile_options(async_signal_handling_watchdog_test)
target_link_libraries(async_signal_handling_watchdog_test monad_core GTest::GTest GTest::Main)
add_test(NAME async_signal_handling_watchdog_test COMMAND ${CMAKE_COMMAND} -E env $<TARGET_FILE:async_signal_handling_watchdog_test>)
set_tests_properties(async_signal_handling_watchdog_test PROPERTIES
  PASS_REGULAR_EXPRESSION ".*FATAL: Unhandled signal SIGPOLL \\(29\\) received, initiating graceful abnormal termination.*"
)
