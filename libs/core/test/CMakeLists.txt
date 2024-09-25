function(monad_add_test target)
  add_executable(${target} ${ARGN})
  monad_compile_options(${target})
  target_link_libraries(${target} monad_core GTest::GTest GTest::Main)
  add_test(NAME ${target} COMMAND $<TARGET_FILE:${target}>)
endfunction()

monad_add_test(allocators_test "allocators.cpp")
monad_add_test(array_test "array.cpp")
monad_add_test(backtrace_test "backtrace.cpp")
monad_add_test(cma_allocators_test "cma_allocators.cpp")
monad_add_test(cpuset_test "cpuset.cpp")
monad_add_test(encode_test "encode_test.cpp")
monad_add_test(fiber_test "fiber.cpp")
monad_add_test(fiber_channel_test "fiber_channel.cpp")
monad_add_test(fiber_semaphore_test "fiber_semaphore.cpp")
monad_add_test(hugemem_test "huge_mem.cpp")
target_link_libraries(hugemem_test GTest::gmock)
monad_add_test(io_buffers_test "io_buffers.cpp")
monad_add_test(literal_test "literal_test.cpp")
monad_add_test(priority_pool_test "priority_pool_test.cpp")
set_tests_properties(priority_pool_test PROPERTIES RUN_SERIAL TRUE)
monad_add_test(run_queue_test "run_queue_test.cpp")
monad_add_test(spinlock_test "spinlock.cpp")
monad_add_test(spinlock_all_options_test "spinlock.cpp")
target_compile_definitions(
  spinlock_all_options_test
  PRIVATE MONAD_SPINLOCK_TRACK_OWNER_INFO MONAD_SPINLOCK_TRACK_STATS
          MONAD_SPINLOCK_TRACK_STATS_ATOMIC)
monad_add_test(unordered_map_test "unordered_map.cpp")

# Ensure the API demo described in fiber-api.md compiles. This was written as
# a C program but must compile as C++ for now because of a Boost.Outcome issue
add_executable(fiber-hello fiber-hello.cpp)
monad_compile_options(fiber-hello)
target_link_libraries(fiber-hello PRIVATE monad_core)

add_executable(fiber_benchmark fiber_bench.cpp)
monad_compile_options(fiber_benchmark)
target_link_libraries(fiber_benchmark PRIVATE monad_core)
