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
  monad_core
  FAIL_REGEX
  ".*Must fail after this:\nFATAL: no i/o buffers remaining.*")
monad_add_test_death(
  io_death_read_buffer_exhaustion_causes_death_test
  SOURCES
  "io_death_read_buffer_exhaustion_causes_death.cpp"
  LINK_LIBRARIES
  monad_async
  monad_core
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
