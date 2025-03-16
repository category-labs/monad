function(monad_test target)
  add_executable(monad_fiber_c_${target} ${ARGN})
  target_compile_features(monad_fiber_c_${target} PRIVATE cxx_std_23)
  target_link_libraries(monad_fiber_c_${target}
                        PRIVATE monad_fiber_c monad_core GTest::GTest GTest::Main)
  gtest_discover_tests(
    monad_fiber_c_${target}
    TEST_PREFIX RunLoop/
    PROPERTIES ENVIRONMENT ASAN_OPTIONS=abort_on_error=1 ENVIRONMENT
               UBSAN_OPTIONS=halt_on_error=1,print_stacktrace=1 ENVIRONMENT
               TSAN_OPTIONS=external_symbolizer_path=/usr/bin/llvm-symbolizer)
endfunction()

monad_test(basic_test "basic.cpp")
monad_test(channel_test "channel.cpp")
monad_test(priority_pool_test "priority_pool.cpp")
set_target_properties(monad_fiber_c_priority_pool_test PROPERTIES RUN_SERIAL ON)
monad_test(run_queue_test "run_queue.cpp")
monad_test(semaphore_test "semaphore.cpp")

target_link_libraries(monad_fiber_c_priority_pool_test PRIVATE monad_fiber)

# Ensure the API demo described in fiber-api.md compiles. This was written as
# a C program but must compile as C++ for now because of a Boost.Outcome issue
add_executable(fiber-hello fiber-hello.cpp)
monad_compile_options(fiber-hello)
target_link_libraries(fiber-hello PRIVATE monad_fiber_c monad_core)

add_executable(fiber_benchmark fiber_bench.cpp)
monad_compile_options(fiber_benchmark)
target_link_libraries(fiber_benchmark monad_fiber_c monad_core)
