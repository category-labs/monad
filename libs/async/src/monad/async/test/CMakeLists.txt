find_package(
  Boost
  CONFIG REQUIRED COMPONENTS fiber)

add_async_test(TARGET io_test SOURCES "io.cpp")

monad_add_test_death(
  io_death_write_buffer_exhaustion_causes_death_test
  SOURCES
  "io_death_write_buffer_exhaustion_causes_death.cpp"
  LINK_LIBRARIES
  monad_async
  FAIL_REGEX
  ".*Must fail after this:\nFATAL: no i/o buffers remaining.*")
monad_add_test_death(
  io_death_read_buffer_exhaustion_causes_death_test
  SOURCES
  "io_death_read_buffer_exhaustion_causes_death.cpp"
  LINK_LIBRARIES
  monad_async
  FAIL_REGEX
  ".*Must fail after this:\nFATAL: no i/o buffers remaining.*")

add_async_test(
  TARGET
  sender_receiver_test
  SOURCES
  "sender_receiver.cpp"
  TEST_FILTER
  "-AsyncIO.timed_delay_sender_receiver:-AsyncIO.external_thread_sender_receiver"
)
if(NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  # explodes build times if optimising
  target_compile_options(sender_receiver_test
                         PRIVATE "-fno-var-tracking-assignments")
endif()
target_link_libraries(sender_receiver_test PRIVATE Boost::fiber)

add_async_test(TARGET storage_pool_test SOURCES "storage_pool.cpp")
